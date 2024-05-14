/*******************************************************************************
 * Copyright (c) 2024 Jorge Navarro Ortiz, University of Granada
 * Based on the work from Thomas Telkamp and Matthijs Kooijman
 *******************************************************************************/

#define TTGO
//#define HELTEC
//#define PYCOM

#include <esp_task_wdt.h>
#define WDT_TIMEOUT 60        // define a 60 seconds WDT (Watch Dog Timer)

#include <WiFi.h>             // Wifi library
#include "esp_wpa2.h"         // WPA2 library for connections to Enterprise networks
#include <HTTPClient.h>       // For HTTPS
#include <WiFiClientSecure.h>
#include <WiFiClient.h>       // For web updater OTA
#include <WebServer.h>
#include <ESPmDNS.h>
#include <Update.h>

#include <lmic.h>             // For LORaWAN
#include <hal/hal.h>
#include <SPI.h>

#include <Wire.h>             // For display
#include "SSD1306.h"
#include "images.h"

#include <math.h>

//#define bOTA 1;

const String version = "1.1";
_dr_eu868_t selectedSF = DR_SF7;    // Spreading factor for the transmissions
double TX_INTERVAL = 20;            // Schedule TX every this many seconds (might become longer due to duty cycle limitations).
double lastTxTime=-1.0;
double currentTxTime=-1.0;
int lastChannel=-1.0;
int currentChannel=-1.0;
double timeToWait = 1000*TX_INTERVAL;    // For the first frames
bool queuedPacket=false;
double timeEnqueue=-1.0;
double timeSent=-1.0;
int FRAME_LENGTH=10;

bool bBoot = true;

SSD1306 display(0x3c, 4, 15);

// LoRaWAN end-device address (DevAddr) and session keys
typedef struct {
  int nodeNumber;
  uint64_t chipid;
  u4_t DevAddr;
  String DevEUI;
  String Model;
} deviceDataStruct;

static const int noDevices = 23;
static deviceDataStruct devicesData[noDevices] = {
  { 1, 0xBD3C8E2DE6B4, 0x00000065, "0000000000000065", "TTGO LORA32"},
  { 2, 0x79458E2DE6B4, 0x00000066, "0000000000000066", "TTGO LORA32"},
  { 3, 0x09408E2DE6B4, 0x00000067, "0000000000000067", "TTGO LORA32"},
  { 4, 0x51458E2DE6B4, 0x00000068, "0000000000000068", "TTGO LORA32"},
  { 5, 0xB93F8E2DE6B4, 0x00000069, "0000000000000069", "TTGO LORA32"},
  { 6, 0x993C8E2DE6B4, 0x0000006A, "000000000000006A", "TTGO LORA32"},
  { 7, 0x5CFA73A4AE30, 0x0000006B, "000000000000006B", "TTGO LORA32"},
  { 8, 0x9D3C8E2DE6B4, 0x0000006C, "000000000000006C", "TTGO LORA32"},
  { 9, 0x09458E2DE6B4, 0x0000006D, "000000000000006D", "TTGO LORA32"},
  {10, 0xA93C8E2DE6B4, 0x0000006E, "000000000000006E", "TTGO LORA32"},
  {11, 0x71438E2DE6B4, 0x0000006F, "000000000000006F", "TTGO LORA32"},
  {12, 0xE93F8E2DE6B4, 0x00000070, "0000000000000070", "TTGO LORA32"},
  {13, 0x0D458E2DE6B4, 0x00000071, "0000000000000071", "TTGO LORA32"},
  {14, 0xC1DD8E2DE6B4, 0x00000072, "0000000000000072", "TTGO LORA32"},
  {15, 0xADDD8E2DE6B4, 0x00000073, "0000000000000073", "TTGO LORA32"},
  {16, 0x45438E2DE6B4, 0x00000074, "0000000000000074", "TTGO LORA32"},
  {17, 0xA4D143A4AE30, 0x00000075, "0000000000000075", "TTGO LORA32"},
  {18, 0xED3F8E2DE6B4, 0x00000076, "0000000000000076", "TTGO LORA32"},
  {19, 0xF53D8E2DE6B4, 0x00000077, "0000000000000077", "TTGO LORA32"},
  {20, 0xE13F8E2DE6B4, 0x00000078, "0000000000000078", "HELTEC WIRELESS STICK"},
  {21, 0xD096FE7EB994, 0x000000C9, "00000000000000C9", "HELTEC WIRELESS STICK"},
  {22, 0x0896FE7EB994, 0x000000CA, "00000000000000CA", "PYCOM FIPY"},
  {23, 0x9D41C33A7D80, 0x0000012D, "000000000000012D", "PYCOM FIPY"}
};
deviceDataStruct deviceData;

static const PROGMEM u1_t NWKSKEY[16] = { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
static const u1_t PROGMEM APPSKEY[16] = { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };

// These callbacks are only used in over-the-air activation, so they are left empty here (we cannot leave them out completely unless
// DISABLE_JOIN is set in config.h, otherwise the linker will complain).
void os_getArtEui (u1_t* buf) { }
void os_getDevEui (u1_t* buf) { }
void os_getDevKey (u1_t* buf) { }

unsigned int counter = 0;
//static uint8_t mydata[] = "TTGO #" STR(TTGONODE);
static uint8_t mydata[256];
int mydata_length;
static osjob_t sendjob;

#ifdef TTGO
// Pin mapping for the Heltec ESP32 Lora board / TTGO Lora32 with 3D metal antenna
const lmic_pinmap lmic_pins = {
    .nss = 18,
    .rxtx = LMIC_UNUSED_PIN,
    .rst = 14,
    .dio = {26, 33, 32}
};
#endif

#ifdef HELTEC
// Pin mapping for the Heltec Wireless Stick
const lmic_pinmap lmic_pins = {
    .nss = 18,
    .rxtx = LMIC_UNUSED_PIN,
    .rst = 14,
    .dio = {26, 35, 34}
};
#endif

#ifdef PYCOM
// Pin mapping for the Pycom FiPy (https://forum.pycom.io/topic/3403/wiring-of-dio-pins-of-lora-sx127x-chip-to-esp32/5)
const lmic_pinmap lmic_pins = {
//  .mosi = 27,
//  .miso = 19,
//  .sck = 5,
  .nss = 18,
  .rxtx = LMIC_UNUSED_PIN,
  .rst = LMIC_UNUSED_PIN,
  .dio = {23, 23, 23}, //workaround to use 1 pin for all 3 radio dio pins
};
#endif

struct transmissionParameters {
    int channel;
    int sf;
    int channel_mask;
    int sf_mask;
    String arrival_distribution;
    double arrival_param1;
    double arrival_param2;
    String frame_distribution;
    double frame_param1;
    double frame_param2;
};
struct transmissionParameters transmissionParams;

#ifdef bOTA
// Related to web updater OTA
char* host = "esp32";
WebServer server(80);

/* Style */
String style =
  "<style>#file-input,input{width:100%;height:44px;border-radius:4px;margin:10px auto;font-size:15px}"
  "input{background:#f1f1f1;border:0;padding:0 15px}body{background:#3498db;font-family:sans-serif;font-size:14px;color:#777}"
  "#file-input{padding:0;border:1px solid #ddd;line-height:44px;text-align:left;display:block;cursor:pointer}"
  "#bar,#prgbar{background-color:#f1f1f1;border-radius:10px}#bar{background-color:#3498db;width:0%;height:10px}"
  "form{background:#fff;max-width:258px;margin:75px auto;padding:30px;border-radius:5px;text-align:center}"
  ".btn{background:#3498db;color:#fff;cursor:pointer}</style>";

  /* Login page */
  String loginIndex = 
  "<form name=loginForm>"
  "<h1>ESP32 Login</h1>"
  "<input name=userid placeholder='User ID'> "
  "<input name=pwd placeholder=Password type=Password> "
  "<input type=submit onclick=check(this.form) class=btn value=Login></form>"
  "<script>"
  "function check(form) {"
  "if(form.userid.value=='admin' && form.pwd.value=='5GLaboratory')"
  "{window.open('/serverIndex')}"
  "else"
  "{alert('Error Password or Username')}"
  "}"
  "</script>" + style;
  
  /* Server Index Page */
String serverIndex = 
  "<script src='https://ajax.googleapis.com/ajax/libs/jquery/3.2.1/jquery.min.js'></script>"
  "<form method='POST' action='#' enctype='multipart/form-data' id='upload_form'>"
  "<input type='file' name='update' id='file' onchange='sub(this)' style=display:none>"
  "<label id='file-input' for='file'>   Choose file...</label>"
  "<input type='submit' class=btn value='Update'>"
  "<br><br>"
  "<div id='prg'></div>"
  "<br><div id='prgbar'><div id='bar'></div></div><br></form>"
  "<script>"
  "function sub(obj){"
  "var fileName = obj.value.split('\\\\');"
  "document.getElementById('file-input').innerHTML = '   '+ fileName[fileName.length-1];"
  "};"
  "$('form').submit(function(e){"
  "e.preventDefault();"
  "var form = $('#upload_form')[0];"
  "var data = new FormData(form);"
  "$.ajax({"
  "url: '/update',"
  "type: 'POST',"
  "data: data,"
  "contentType: false,"
  "processData:false,"
  "xhr: function() {"
  "var xhr = new window.XMLHttpRequest();"
  "xhr.upload.addEventListener('progress', function(evt) {"
  "if (evt.lengthComputable) {"
  "var per = evt.loaded / evt.total;"
  "$('#prg').html('progress: ' + Math.round(per*100) + '%');"
  "$('#bar').css('width',Math.round(per*100) + '%');"
  "}"
  "}, false);"
  "return xhr;"
  "},"
  "success:function(d, s) {"
  "console.log('success!') "
  "},"
  "error: function (a, b, c) {"
  "}"
  "});"
  "});"
  "</script>" + style;
#endif


//////////////////////////////////////
// FUNCTIONS RELATED TO DEVICE DATA //
//////////////////////////////////////
void initializeDeviceData(uint64_t chipid) {
  int indexOfDevice = -1;
  for (int i=0; i<noDevices; i++) {
    if (chipid == devicesData[i].chipid) {
      indexOfDevice = i;
      break;
    }
  }
  deviceData = devicesData[indexOfDevice];
}


/////////////////////////////////////////////
// FUNCTIONS RELATED TO WI-FI CONNECTIVITY //
/////////////////////////////////////////////
void connectToWiFiEduroam() {
  //Identity for user with password related to his realm (organization)
  //Available option of anonymous identity for federation of RADIUS servers or 1st Domain RADIUS servers
  #define EAP_ANONYMOUS_IDENTITY "anonymous2022@ugr.es"
  #define EAP_IDENTITY "xxx@ugr.es"
  #define EAP_PASSWORD "xxx"
  #define EAP_USERNAME "xxx@ugr.es"
  //SSID NAME
  const char* ssid = "eduroam"; // eduroam SSID

/*const static char* test_root_ca PROGMEM = \
    "-----BEGIN CERTIFICATE-----\n" \
    "MIIF7zCCBFegAwIBAgIUEiuH99MA7028+Lyliv5d+AkBJP0wDQYJKoZIhvcNAQEL\n" \
    "BQAwgZAxCzAJBgNVBAYTAkVTMRAwDgYDVQQIDAdHcmFuYWRhMRAwDgYDVQQHDAdH\n" \
    "cmFuYWRhMR8wHQYDVQQKDBZVbml2ZXJzaWRhZCBkZSBHcmFuYWRhMRswGQYJKoZI\n" \
    "hvcNAQkBFgxyZWRlc0B1Z3IuZXMxHzAdBgNVBAMMFkFDIGRlIFVHUiBwYXJhIGVk\n" \
    "dXJvYW0wHhcNMjIwMzE4MDkyMDI3WhcNNDIwMzEzMDkyMDI3WjCBkDELMAkGA1UE\n" \
    "BhMCRVMxEDAOBgNVBAgMB0dyYW5hZGExEDAOBgNVBAcMB0dyYW5hZGExHzAdBgNV\n" \
    "BAoMFlVuaXZlcnNpZGFkIGRlIEdyYW5hZGExGzAZBgkqhkiG9w0BCQEWDHJlZGVz\n" \
    "QHVnci5lczEfMB0GA1UEAwwWQUMgZGUgVUdSIHBhcmEgZWR1cm9hbTCCAaIwDQYJ\n" \
    "KoZIhvcNAQEBBQADggGPADCCAYoCggGBAO3brYn2RE1Khfr0zLSE19rfISVDJ5np\n" \
    "+ceCK76aqp94SxetCO7ZlrVGNgE0LAh0L6s1VHc2Kg+a1zIW8rD8UIb2m7nVV6wY\n" \
    "tg4TLmV1xx+LhWaZXJuZfKldx+B44PxQ16m7rntF52v3FHiDSAeT0L4KBhPpPROx\n" \
    "T/ed/p5sImmKyo6yO02wmwxS28cwaW8EP3xiEEEViaeswTXqlMQERdWoj67fnNS3\n" \
    "gq08NfJHOwV0GRM0aP+fxL0xwhNmg6M0icp6ruj5l+KggRej6Dn6x7Ab/mIFc16j\n" \
    "LvQvCoVlnlAL5zByLmKiBI8WJvBGxKc8iTmdFlpjabuS8B80DhjYfikvrJxD7W8H\n" \
    "ZDvQMGMZGItvZp4fnzlXvCgQUfKwfbWt83FdiLbufjslWpq+hazz1Au5cpFe8web\n" \
    "Fze9uO0vmra+lHEy21VP3gY4QQ6QM7pstCN7q8jmmcwBiYg9gD0Hhr0y4wqyBt0Y\n" \
    "Yqbwuy3n8t1/e92FkHtFdTK+sH22RWTrfQIDAQABo4IBPTCCATkwHQYDVR0OBBYE\n" \
    "FCl+19cZu8KuIx96l3miii7wbJPXMIHQBgNVHSMEgcgwgcWAFCl+19cZu8KuIx96\n" \
    "l3miii7wbJPXoYGWpIGTMIGQMQswCQYDVQQGEwJFUzEQMA4GA1UECAwHR3JhbmFk\n" \
    "YTEQMA4GA1UEBwwHR3JhbmFkYTEfMB0GA1UECgwWVW5pdmVyc2lkYWQgZGUgR3Jh\n" \
    "bmFkYTEbMBkGCSqGSIb3DQEJARYMcmVkZXNAdWdyLmVzMR8wHQYDVQQDDBZBQyBk\n" \
    "ZSBVR1IgcGFyYSBlZHVyb2FtghQSK4f30wDvTbz4vKWK/l34CQEk/TAPBgNVHRMB\n" \
    "Af8EBTADAQH/MDQGA1UdHwQtMCswKaAnoCWGI2h0dHBzOi8vY3NpcmMudWdyLmVz\n" \
    "L2VkdXJvYW1fY2EuY3JsMA0GCSqGSIb3DQEBCwUAA4IBgQDVf2FvEzXWilibsGjD\n" \
    "xUQDIojQ7X8JbgiL/+DHhBzr9EzXsUchi/E1Y6FwQ/BLkX//k5ttTudVqYv3rT1M\n" \
    "cu0f5ZsHuO6Q+DDdbWtKoMNaQqrpy+CcYaes0V/i8iaJqi9uju0pdrRQzOjXBd7O\n" \
    "IiArC6UY0BjI6e13DW5UDrZVzrl1X8oH+0/82BcQiCWlSVV9wltTUDF3i+XAnm3j\n" \
    "apzpVjOizkJpupxmiFSNW3+uccf4yLSp2a/E/8wwIA2BuYlNI7cRlYXOYWN6N71f\n" \
    "irFqYnHgvfOScRTSPkFkWMoesvuFql38tFSINbtLX9ykl5mGm4atBDZgcI3/pZ1R\n" \
    "4AZB84PAIUp2PurMff3UgjrZBMZPngOWVYlLb1+mCmUs4ssz0xpXW4+HbGZHCo90\n" \
    "ww9ma5VioXqMqJLPngIZZpb4FprrG/aYqm7Jl1ZNnDM/ZMlaWrG3s3kyn46psy9O\n" \
    "IJjs9pBoiUd2QTEr2jrkrrA2ImuwAMd00ys7SUqToiN3zvw=\n" \
    "-----END CERTIFICATE-----\n";*/

  WiFi.disconnect(true);  //disconnect from WiFi to set new WiFi connection
  //WiFi.begin(ssid, WPA2_AUTH_PEAP, EAP_ANONYMOUS_IDENTITY, EAP_IDENTITY, EAP_PASSWORD, test_root_ca); //with CERTIFICATE 
  WiFi.begin(ssid, WPA2_AUTH_PEAP, EAP_IDENTITY, EAP_USERNAME, EAP_PASSWORD); // without CERTIFICATE, RADIUS server EXCEPTION "for old devices" required
}

void connectToWiFiHome() {
  WiFi.mode(WIFI_STA);
  //WiFi.begin("WAP", "xxx");
  WiFi.begin("xxx", "xxx");
}

void connectToWiFi() {
  bool bFound = false;

  while (!bFound) {
    int n = WiFi.scanNetworks();
    bool bEduroam = false;
    bool bHome = false;

    for (int i = 0; i < n; ++i) {
      if (WiFi.SSID(i) == "eduroam") {
        bEduroam = true;
        bFound = true;
        Serial.println("Found eduroam network!");
      } else if (WiFi.SSID(i) == "xxx") {
        bHome = true;
        bFound = true;
        Serial.println("Found home network!");
      }
    }
    if (bEduroam) {
      connectToWiFiEduroam();
    }
    if (bHome) {
      connectToWiFiHome();
    }
  }
}

void waitForWiFiConnection() {
  int i=0;
  //while (WiFi.status() != WL_CONNECTED) { // This does not work with Eduroam!!!
    while (WiFi.localIP().toString() == "0.0.0.0") {
    i=i+1;
/*    if (i % 20 == 0) {
      //ESP.restart();
      connectToWiFi();
    }
*/
    delay(1000);
/*    if (i % 20 == 0) {
      Serial.print(F("R")); // retry
    } else {
*/
      Serial.print(F(".")); // waiting
/*    }
*/
    //Serial.println("WiFi.status():  " + String(WiFi.status()));
    //Serial.println("WiFi.localIP(): " + WiFi.localIP().toString());
  }
  Serial.println("");
  Serial.println(F(">>> WiFi is connected!"));
  Serial.println(">>> IP address: " + WiFi.localIP().toString());
}

void WiFiEvent(WiFiEvent_t event)
{
    Serial.printf("[WiFi-event] event: %d\n", event);

    switch (event) {
        case ARDUINO_EVENT_WIFI_READY: 
            Serial.println("WiFi interface ready");
            break;
        case ARDUINO_EVENT_WIFI_SCAN_DONE:
            Serial.println("Completed scan for access points");
            break;
        case ARDUINO_EVENT_WIFI_STA_START:
            Serial.println("WiFi client started");
            break;
        case ARDUINO_EVENT_WIFI_STA_STOP:
            Serial.println("WiFi clients stopped");
            break;
        case ARDUINO_EVENT_WIFI_STA_CONNECTED:
            Serial.println("Connected to access point");
            break;
        case ARDUINO_EVENT_WIFI_STA_DISCONNECTED:
            Serial.println("Disconnected from WiFi access point. Trying to reconnect.");
            connectToWiFi();
            break;
        case ARDUINO_EVENT_WIFI_STA_AUTHMODE_CHANGE:
            Serial.println("Authentication mode of access point has changed");
            break;
        case ARDUINO_EVENT_WIFI_STA_GOT_IP:
            Serial.print("Obtained IP address: ");
            Serial.println(WiFi.localIP());
            break;
        case ARDUINO_EVENT_WIFI_STA_LOST_IP:
            Serial.println("Lost IP address and IP address is reset to 0");
            break;
        case ARDUINO_EVENT_WPS_ER_SUCCESS:
            Serial.println("WiFi Protected Setup (WPS): succeeded in enrollee mode");
            break;
        case ARDUINO_EVENT_WPS_ER_FAILED:
            Serial.println("WiFi Protected Setup (WPS): failed in enrollee mode");
            break;
        case ARDUINO_EVENT_WPS_ER_TIMEOUT:
            Serial.println("WiFi Protected Setup (WPS): timeout in enrollee mode");
            break;
        case ARDUINO_EVENT_WPS_ER_PIN:
            Serial.println("WiFi Protected Setup (WPS): pin code in enrollee mode");
            break;
        case ARDUINO_EVENT_WIFI_AP_START:
            Serial.println("WiFi access point started");
            break;
        case ARDUINO_EVENT_WIFI_AP_STOP:
            Serial.println("WiFi access point  stopped");
            break;
        case ARDUINO_EVENT_WIFI_AP_STACONNECTED:
            Serial.println("Client connected");
            break;
        case ARDUINO_EVENT_WIFI_AP_STADISCONNECTED:
            Serial.println("Client disconnected");
            break;
        case ARDUINO_EVENT_WIFI_AP_STAIPASSIGNED:
            Serial.println("Assigned IP address to client");
            break;
        case ARDUINO_EVENT_WIFI_AP_PROBEREQRECVED:
            Serial.println("Received probe request");
            break;
        case ARDUINO_EVENT_WIFI_AP_GOT_IP6:
            Serial.println("AP IPv6 is preferred");
            break;
        case ARDUINO_EVENT_WIFI_STA_GOT_IP6:
            Serial.println("STA IPv6 is preferred");
            break;
        case ARDUINO_EVENT_ETH_GOT_IP6:
            Serial.println("Ethernet IPv6 is preferred");
            break;
        case ARDUINO_EVENT_ETH_START:
            Serial.println("Ethernet started");
            break;
        case ARDUINO_EVENT_ETH_STOP:
            Serial.println("Ethernet stopped");
            break;
        case ARDUINO_EVENT_ETH_CONNECTED:
            Serial.println("Ethernet connected");
            break;
        case ARDUINO_EVENT_ETH_DISCONNECTED:
            Serial.println("Ethernet disconnected");
            break;
        case ARDUINO_EVENT_ETH_GOT_IP:
            Serial.println("Obtained IP address");
            break;
        default: break;
    }}

// WARNING: This function is called from a separate FreeRTOS task (thread)!
void WiFiGotIP(WiFiEvent_t event, WiFiEventInfo_t info)
{
    Serial.print("[INFO] WiFi connected, IP address: ");
    Serial.println(IPAddress(info.got_ip.ip_info.ip.addr));
}


//////////////////////////////////////
// FUNCTIONS RELATED TO THE DISPLAY // 
//////////////////////////////////////
void logo(){
  display.clear();
  display.drawXbm(35,12,LoRa_Logo_width,LoRa_Logo_height,LoRa_Logo_bits);
  display.display();
}


//////////////////////////////////
// FUNCTIONS RELATED TO LORAWAN //
//////////////////////////////////
void initializeFrameBuffer() {
  for (int i=0; i<sizeof(mydata); i++) {
    mydata[i]=0;
  }
}

double RandomGauss(double mean, double stdev) {
  // See https://en.wikipedia.org/wiki/Box%E2%80%93Muller_transform
  double r1 = random(1e6) / 1.0e6;
  double r2 = random(1e6) / 1.0e6;
  double Z = sqrt(-2*log(r1))*cos(2*M_PI*r2);
  double X = Z * stdev + mean;
  //Serial.println("r1: " + String(r1));
  //Serial.println("r2: " + String(r2));
  //Serial.println("Z: " + String(Z));
  //Serial.println("X: " + String(X));
  return X;
}

void setFrameContent() {
//mydata
//mydata_length

  // Testing
  //transmissionParams.frame_distribution = "normal";

  if (transmissionParams.frame_distribution == "uniform") {
    if (abs(transmissionParams.frame_param1 - transmissionParams.frame_param2) < 0.001) {
      mydata_length = transmissionParams.frame_param1;
    }
    double randDouble = random(1000*transmissionParams.frame_param1, 1000*transmissionParams.frame_param2) / 1000.0;
    //Serial.println("randDouble: " + String(randDouble));
    mydata_length = randDouble;
  } else if (transmissionParams.frame_distribution == "normal") {
    double randDouble = RandomGauss(transmissionParams.frame_param1, transmissionParams.frame_param2);
    mydata_length = int(randDouble);
    //mydata_length = transmissionParams.frame_param1;
  }

  // Frame size limited by 6 bytes (counter) and 51 bytes (maximum frame size for SF7)
  if (mydata_length < 6) {
    mydata_length = 6;
  } else if (mydata_length > 51) {
    mydata_length = 51;
  }

  Serial.println("frame size: " + String(mydata_length));

  mydata[0]=1; // Channel 1
  mydata[1]=1; // Data type 1 (counter)
  unsigned int aux=counter; 
  mydata[5]=aux;
  aux <<= 8; mydata[4]=aux;
  aux <<= 8; mydata[3]=aux;
  aux <<= 8; mydata[2]=aux;
  // The rest of the frame buffer is set to 0 in the initializeFrameBuffer() function
}

dr_t convertSF2DR(int sf) {
  //enum _dr_eu868_t { DR_SF12=0, DR_SF11, DR_SF10, DR_SF9, DR_SF8, DR_SF7, DR_SF7B, DR_FSK, DR_NONE };
  return 12 - sf;
}

u4_t getFrequency(int channel) {
  u4_t freq;
  switch(channel) {
    case 1:
      freq = 868100000;
      break;
    case 2:
      freq = 868300000;
      break;
    case 3:
      freq = 868500000;
      break;
    case 4:
      freq = 867100000;
      break;
    case 5:
      freq = 867300000;
      break;
    case 6:
      freq = 867500000;
      break;
    case 7:
      freq = 867700000;
      break;
    case 8:
      freq = 867900000;
      break;
    default:
      freq = 868100000;
      break;
  }

  return freq;
}

void setChannel(int channel) {
  if (currentChannel != lastChannel) {
    // Disable all channels
    for(int i=0; i<9; i++) { // For EU; for US use i<71
      if(i != channel) {
        LMIC_disableChannel(i);
     }
    }

    if (channel == 0) {
      // Add all channels, periodic channel selection
      // Set up the channels used in Europe (868 MHz band)
      LMIC_setupChannel(0, 868100000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(1, 868300000, DR_RANGE_MAP(DR_SF12, DR_SF7B), BAND_CENTI);      // g-band
      LMIC_setupChannel(2, 868500000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(3, 867100000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(4, 867300000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(5, 867500000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(6, 867700000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(7, 867900000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(8, 868800000, DR_RANGE_MAP(DR_SF12, DR_FSK),  BAND_MILLI);      // g2-band
    } else {
      // Set same frequency for all channels
      u4_t freq = getFrequency(channel);
      LMIC_setupChannel(0, freq, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(1, freq, DR_RANGE_MAP(DR_SF12, DR_SF7B), BAND_CENTI);      // g-band
      LMIC_setupChannel(2, freq, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(3, freq, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(4, freq, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(5, freq, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(6, freq, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(7, freq, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
      LMIC_setupChannel(8, freq, DR_RANGE_MAP(DR_SF12, DR_FSK),  BAND_MILLI);      // g2-band
    }
  }
}

void onEvent (ev_t ev) {
    Serial.print(os_getTime());
    Serial.print(": ");
    switch(ev) {
        case EV_SCAN_TIMEOUT:
            Serial.println(F("EV_SCAN_TIMEOUT"));
            break;
        case EV_BEACON_FOUND:
            Serial.println(F("EV_BEACON_FOUND"));
            break;
        case EV_BEACON_MISSED:
            Serial.println(F("EV_BEACON_MISSED"));
            break;
        case EV_BEACON_TRACKED:
            Serial.println(F("EV_BEACON_TRACKED"));
            break;
        case EV_JOINING:
            Serial.println(F("EV_JOINING"));
            break;
        case EV_JOINED:
            Serial.println(F("EV_JOINED"));
            break;
        case EV_RFU1:
            Serial.println(F("EV_RFU1"));
            break;
        case EV_JOIN_FAILED:
            Serial.println(F("EV_JOIN_FAILED"));
            break;
        case EV_REJOIN_FAILED:
            Serial.println(F("EV_REJOIN_FAILED"));
            break;
        case EV_TXCOMPLETE:
            counter++;
            queuedPacket = false;
            Serial.println(F("EV_TXCOMPLETE (includes waiting for RX windows)"));
            if (LMIC.txrxFlags & TXRX_ACK)
              Serial.println(F("Received ack"));
            if (LMIC.dataLen) {
              Serial.print(F("Received "));
              Serial.print(LMIC.dataLen);
              Serial.println(F(" bytes of payload"));
            }
            // Schedule next transmission
            //os_setTimedCallback(&sendjob, os_getTime()+sec2osticks(TX_INTERVAL), do_send);
            timeSent = millis();
            if (lastTxTime > 0) {
                currentTxTime = millis();
                double timeBetweenLastTwoFrames = currentTxTime-lastTxTime;
                double timeBetweenEnqueueAndSend = timeSent-timeEnqueue;
                //timeToWait = TX_INTERVAL + (TX_INTERVAL - timeBetweenLastTwoFrames);
                timeToWait = 1000*TX_INTERVAL - timeBetweenEnqueueAndSend;
                //Serial.println("currentTxTime:                      " + String(currentTxTime) + " msec");
                //Serial.println("lastTxTime:                         " + String(lastTxTime) + " msec");
//                Serial.println("Time between last two packets:      " + String(timeBetweenLastTwoFrames/1000) + " sec");
                //Serial.println("timeSent:                           " + String(timeSent) + " msec");
                //Serial.println("timeEnqueue:                        " + String(timeEnqueue) + " msec");
//                Serial.println("Time between enqueuing and sending: " + String(timeBetweenEnqueueAndSend/1000) + " sec");
                Serial.println("Time to wait for next frame:        " + String(timeToWait/1000) + " sec");
                lastTxTime=currentTxTime;
            } else {
                lastTxTime = millis();
            }

            //convertSF2DR
            LMIC_setDrTxpow(convertSF2DR(transmissionParams.sf),14);
            //LMIC_setDrTxpow(DR_SF7,14);

            currentChannel = transmissionParams.channel;
            setChannel(currentChannel);

            os_setTimedCallback(&sendjob, os_getTime()+sec2osticks(timeToWait/1000), do_send);
            break;
        case EV_LOST_TSYNC:
            Serial.println(F("EV_LOST_TSYNC"));
            break;
        case EV_RESET:
            Serial.println(F("EV_RESET"));
            break;
        case EV_RXCOMPLETE:
            // data received in ping slot
            Serial.println(F("EV_RXCOMPLETE"));
            break;
        case EV_LINK_DEAD:
            Serial.println(F("EV_LINK_DEAD"));
            break;
        case EV_LINK_ALIVE:
            Serial.println(F("EV_LINK_ALIVE"));
            break;
        default:
            Serial.println(F("Unknown event"));
            break;
    }
}

void do_send(osjob_t* j){
    // Check if there is not a current TX/RX job running
    if (LMIC.opmode & OP_TXRXPEND) {
        Serial.println(F("OP_TXRXPEND, not sending"));
    } else {
        timeEnqueue = millis();
        setFrameContent();
        // Prepare upstream data transmission at the next possible time.
        //LMIC_setTxData2(1, mydata, sizeof(mydata)-1, 0);
        Serial.print("[INFO] Data length: "); Serial.println(mydata_length);
        LMIC_setTxData2(1, mydata, mydata_length, 0);
        Serial.println(F("Packet queued"));
        queuedPacket = true;
    }
    // Next TX is scheduled after TX_COMPLETE event.

    lastChannel = currentChannel;

    transmissionParams = getDefaultTransmissionParameters();
    /*if (WiFi.localIP().toString() != "0.0.0.0") {
        transmissionParams = getTransmissionParameters();
    }*/
    //LMIC_setDrTxpow(DR_SF7,14);
    //LMIC_setDrTxpow(8,14); // *** CHANGE SF ***
}

struct transmissionParameters getDefaultTransmissionParameters() {

  // Default values
  struct transmissionParameters txparams;
  txparams.channel = 0;
  txparams.sf = 7;
  txparams.channel_mask = 255;
  txparams.sf_mask = 255;
  txparams.arrival_distribution = "uniform";
  txparams.arrival_param1 = 20.0;
  txparams.arrival_param2 = 20.0;
  txparams.frame_distribution = "uniform";
  txparams.frame_param1 = 10.0;
  txparams.frame_param2 = 10.0;
  
  return txparams;
}

struct transmissionParameters getTransmissionParameters() {

  // Default values
  struct transmissionParameters txparams;
  txparams.channel = 0;
  txparams.sf = 7;
  txparams.channel_mask = 255;
  txparams.sf_mask = 255;
  txparams.arrival_distribution = "uniform";
  txparams.arrival_param1 = 20.0;
  txparams.arrival_param2 = 20.0;
  txparams.frame_distribution = "uniform";
  txparams.frame_param1 = 10.0;
  txparams.frame_param2 = 10.0;

  //return txparams;

const char* rootCACertificate = \
"-----BEGIN CERTIFICATE-----\n" \
"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\n" \
"-----END CERTIFICATE-----\n";

  String strs[32];
  int StringCount = 0;

  WiFiClientSecure *client = new WiFiClientSecure;
  if(client) {
    client -> setCACert(rootCACertificate);

    {
      // Add a scoping block for HTTPClient https to make sure it is destroyed before WiFiClientSecure *client is 
      HTTPClient https;
  
      int reset = 0;
      if (bBoot) {
        bBoot = false;
        reset = 1;
      }

      //Serial.print("[HTTPS] begin...\n");
      String request = "https://loragran.ugr.es/devices/get_transmission_parameters.php?deveui=" + deviceData.DevEUI + "&version=" + version + "&reset=" + reset;
      Serial.println ("[HTTPS] GET request: " + request);
      if (https.begin(*client, request)) {  // HTTPS
        //Serial.print("[HTTPS] GET...\n");
        // start connection and send HTTP header
        int httpCode = https.GET();
  
        // httpCode will be negative on error
        if (httpCode > 0) {
          // HTTP header has been send and Server response header has been handled
          Serial.printf("[HTTPS] Return code: %d\n", httpCode);
  
          // file found at server
          if (httpCode == HTTP_CODE_OK || httpCode == HTTP_CODE_MOVED_PERMANENTLY) {
            String payload = https.getString();
            Serial.println("Payload: " + payload);

            // Split the string into substrings
            int index = payload.indexOf(':');
            if (index != -1) // value found
              payload = payload.substring(index+1);

            while (payload.length() > 0)
            {
              int index = payload.indexOf(',');
              if (index == -1) // No comma found
              {
                strs[StringCount++] = payload;
                break;
              }
              else
              {
                strs[StringCount++] = payload.substring(0, index);
                payload = payload.substring(index+2); // There is one space after the comma
              }
            }

            txparams.channel             =strs[0].toInt();
            txparams.sf                  =strs[1].toInt();
            txparams.channel_mask        =strs[2].toInt();
            txparams.sf_mask             =strs[3].toInt();
            txparams.arrival_distribution=strs[4];
            txparams.arrival_param1      =strs[5].toDouble();
            txparams.arrival_param2      =strs[6].toDouble();
            txparams.frame_distribution  =strs[7];
            txparams.frame_param1        =strs[8].toDouble();
            txparams.frame_param2        =strs[9].toDouble();
          }
        } else {
          Serial.printf("[HTTPS] GET... failed, error: %s\n", https.errorToString(httpCode).c_str());
        }
  
        https.end();
      } else {
        Serial.printf("[HTTPS] Unable to connect\n");
      }

      // End extra scoping block
    }
  
    delete client;
  } else {
    Serial.println("Unable to create client");
  }

  /*Serial.println("txparams.channel:              " + String(txparams.channel));
  Serial.println("txparams.sf:                   " + String(txparams.sf));
  Serial.println("txparams.channel_mask:         " + String(txparams.channel_mask));
  Serial.println("txparams.sf_mask:              " + String(txparams.sf_mask));
  Serial.println("txparams.arrival_distribution: " + String(txparams.arrival_distribution));
  Serial.println("txparams.arrival_param1:       " + String(txparams.arrival_param1));
  Serial.println("txparams.arrival_param2:       " + String(txparams.arrival_param2));
  Serial.println("txparams.frame_distribution:   " + String(txparams.frame_distribution));
  Serial.println("txparams.frame_param1:         " + String(txparams.frame_param1));
  Serial.println("txparams.frame_param2:         " + String(txparams.frame_param2));
  */

  //txparams.arrival_distribution = "normal";
  if (txparams.arrival_distribution == "uniform") {
    if (abs(txparams.arrival_param1 - txparams.arrival_param2) < 0.001) {
      TX_INTERVAL = txparams.arrival_param1;
    }
    double randDouble = random(1000*txparams.arrival_param1, 1000*txparams.arrival_param2) / 1000.0;
    //Serial.println("randDouble: " + String(randDouble));
    TX_INTERVAL = randDouble;
  } else if (txparams.arrival_distribution == "normal") {
    double randDouble = RandomGauss(txparams.arrival_param1, txparams.arrival_param2);
    // To avoid a time between frame arrivals excesively high (which would means that the node will not transmit again), 
    // we limit the maximum to the mean plus 4 times the standard deviation.
    if (randDouble > (txparams.arrival_param1 + 4 * txparams.arrival_param2)) {
      randDouble = txparams.arrival_param1 + 4 * txparams.arrival_param2;
    }
    TX_INTERVAL = randDouble;
    //TX_INTERVAL = txparams.arrival_param1;
  }
  Serial.println("TX_INTERVAL: " + String(TX_INTERVAL));

  return txparams;
}

void setup() {

    Serial.begin(115200);
    Serial.println("");

    // WatchDog Timer
    esp_task_wdt_init(WDT_TIMEOUT, true);  // enable panic so ESP32 restarts
                                           // reboot if there is no Wi-Fi connection in one minute
    esp_task_wdt_add(NULL);                // add current thread to WDT watch

    Serial.println("\n\nJorge Navarro Ortiz (jorgenavarro@ugr.es), University of Granada, 2024");
    uint64_t chipid=ESP.getEfuseMac(); // The chip ID is essentially its MAC address (length: 6 bytes).
    Serial.printf("\nStartup (ESP32 Chip ID: 0x%04X%08X)\n",(uint16_t)(chipid>>32),(uint32_t)chipid);
    //Serial.println("\nConnecting to Wi-Fi network");

    initializeDeviceData(chipid);
#ifdef TTGO
    Serial.println("Node TTGO #" + String(deviceData.nodeNumber));
#endif
#ifdef HELTEC
    Serial.println("Node HELTEC #" + String(deviceData.nodeNumber));
#endif
    Serial.printf("DevAddr: 0x%08X\n", deviceData.DevAddr);

    // For OLED
    pinMode(16,OUTPUT);
    pinMode(25,OUTPUT);
    digitalWrite(16, LOW);  // set GPIO16 low to reset OLED
    delay(50);
    digitalWrite(16, HIGH); // while OLED is running, must set GPIO16 in high

    display.init();
    //display.flipScreenVertically();
    display.setFont(ArialMT_Plain_10);
    logo();
    delay(1500);

    // Wi-Fi connectivity
    // From https://github.com/espressif/arduino-esp32/blob/master/libraries/WiFi/examples/WiFiClientEvents/WiFiClientEvents.ino
    // Examples of different ways to register wifi events; these handlers will be called from another thread.
    /*WiFi.onEvent(WiFiEvent);
    WiFi.onEvent(WiFiGotIP, WiFiEvent_t::ARDUINO_EVENT_WIFI_STA_GOT_IP);
    WiFiEventId_t eventID = WiFi.onEvent([](WiFiEvent_t event, WiFiEventInfo_t info){
        Serial.print("WiFi lost connection. Reason: ");
        Serial.println(info.wifi_sta_disconnected.reason);
    }, WiFiEvent_t::ARDUINO_EVENT_WIFI_STA_DISCONNECTED);

    connectToWiFi();
    waitForWiFiConnection();
    */

    // For web updater OTA
    /*use mdns for host name resolution*/
#ifdef bOTA
    //if (!MDNS.begin(host)) { //http://esp32.local
  #ifdef TTGO
    if (!MDNS.begin("ttgo" + deviceData.nodeNumber)) { //http://esp32.local
  #endif
  #ifdef HELTEC
    if (!MDNS.begin("heltec" + deviceData.nodeNumber)) { //http://esp32.local
  #endif
  #ifdef PYCOM
    if (!MDNS.begin("pycom" + deviceData.nodeNumber)) { //http://esp32.local
  #endif        Serial.println("Error setting up MDNS responder!");
      while (1) {
        delay(1000);
      }
    }
    Serial.println("mDNS responder started");
    /*return index page which is stored in serverIndex */
    server.on("/", HTTP_GET, []() {
      server.sendHeader("Connection", "close");
      server.send(200, "text/html", loginIndex);
    });
    server.on("/serverIndex", HTTP_GET, []() {
      server.sendHeader("Connection", "close");
      server.send(200, "text/html", serverIndex);
    });
    /*handling uploading firmware file */
    server.on("/update", HTTP_POST, []() {
      server.sendHeader("Connection", "close");
      server.send(200, "text/plain", (Update.hasError()) ? "FAIL" : "OK");
      ESP.restart();
    }, []() {
      HTTPUpload& upload = server.upload();
      if (upload.status == UPLOAD_FILE_START) {
        Serial.printf("Update: %s\n", upload.filename.c_str());
        if (!Update.begin(UPDATE_SIZE_UNKNOWN)) { //start with max available size
          Update.printError(Serial);
        }
      } else if (upload.status == UPLOAD_FILE_WRITE) {
        /* flashing firmware to ESP*/
        if (Update.write(upload.buf, upload.currentSize) != upload.currentSize) {
          Update.printError(Serial);
        }
      } else if (upload.status == UPLOAD_FILE_END) {
        if (Update.end(true)) { //true to set the size to the current progress
          Serial.printf("Update Success: %u\nRebooting...\n", upload.totalSize);
        } else {
          Update.printError(Serial);
        }
      }
    });
    server.begin();
#endif

    // Initialize LoRaWAN frame buffer
    initializeFrameBuffer();

    // LMIC init
    os_init();
    // Reset the MAC state. Session and pending data transfers will be discarded.
    LMIC_reset();

    // Set static session parameters. Instead of dynamically establishing a session
    // by joining the network, precomputed session parameters are be provided.
    #ifdef PROGMEM
    // On AVR, these values are stored in flash and only copied to RAM
    // once. Copy them to a temporary buffer here, LMIC_setSession will
    // copy them into a buffer of its own again.
    uint8_t appskey[sizeof(APPSKEY)];
    uint8_t nwkskey[sizeof(NWKSKEY)];
    memcpy_P(appskey, APPSKEY, sizeof(APPSKEY));
    memcpy_P(nwkskey, NWKSKEY, sizeof(NWKSKEY));
    LMIC_setSession (0x1, deviceData.DevAddr, nwkskey, appskey);
    #else
    // If not running an AVR with PROGMEM, just use the arrays directly
    LMIC_setSession (0x1, deviceData.DevAddr, NWKSKEY, APPSKEY);
    #endif

    // Set up the channels used in Europe (868 MHz band)
    LMIC_setupChannel(0, 868100000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
    LMIC_setupChannel(1, 868300000, DR_RANGE_MAP(DR_SF12, DR_SF7B), BAND_CENTI);      // g-band
    LMIC_setupChannel(2, 868500000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
    LMIC_setupChannel(3, 867100000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
    LMIC_setupChannel(4, 867300000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
    LMIC_setupChannel(5, 867500000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
    LMIC_setupChannel(6, 867700000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
    LMIC_setupChannel(7, 867900000, DR_RANGE_MAP(DR_SF12, DR_SF7),  BAND_CENTI);      // g-band
    LMIC_setupChannel(8, 868800000, DR_RANGE_MAP(DR_SF12, DR_FSK),  BAND_MILLI);      // g2-band

    // Disable link check validation
    LMIC_setLinkCheckMode(0);

    // TTN uses SF9 for its RX2 window.
    LMIC.dn2Dr = DR_SF9;

    // Set data rate and transmit power for uplink (note: txpow seems to be ignored by the library)
    LMIC_setDrTxpow(selectedSF,14);

    esp_task_wdt_init(WDT_TIMEOUT, true);  // enable panic so ESP32 restarts
    esp_task_wdt_add(NULL);                // add current thread to WDT watch

    // Start job
    do_send(&sendjob);
}

void loop() {
    os_runloop_once();

    display.clear();
    display.setTextAlignment(TEXT_ALIGN_LEFT);
    display.setFont(ArialMT_Plain_10);
    display.drawString(0, 0, "Node TTGO #" + String(deviceData.nodeNumber) + ", ABP v" + version);
    uint64_t chipid=ESP.getEfuseMac(); // The chip ID is essentially its MAC address (length: 6 bytes).
    display.drawString(0, 30, "Packets sent: " + String (counter));
    if (queuedPacket) {
        display.drawString(0, 40, "Packet queued!");
    } else {
        display.drawString(0, 40, "Next frame in " + String(timeToWait/1000) + " sec");
    }
    /*display.drawString(0, 20, "IP addr: " + WiFi.localIP().toString());
    if (WiFi.localIP().toString() == "0.0.0.0") {
      display.drawString(0, 10, "Trying to connect to eduroam...");
    }*/
    display.display();

    /*if (WiFi.localIP().toString() == "0.0.0.0") {
      Serial.println("IP address is 0.0.0.0, trying to reconnect to eduroam...");
      connectToWiFi();
    }*/

#ifdef bOTA
    server.handleClient();
    delay(1);
#endif

    esp_task_wdt_reset();            // Added to repeatedly reset the Watch Dog Timer
}
