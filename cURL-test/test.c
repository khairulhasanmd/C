/***************************************************************************
 *                                  _   _ ____  _
 *  Project                     ___| | | |  _ \| |
 *                             / __| | | | |_) | |
 *                            | (__| |_| |  _ <| |___
 *                             \___|\___/|_| \_\_____|
 *
 * Copyright (C) 1998 - 2013, Daniel Stenberg, <daniel@haxx.se>, et al.
 *
 * This software is licensed as described in the file COPYING, which
 * you should have received as part of this distribution. The terms
 * are also available at http://curl.haxx.se/docs/copyright.html.
 *
 * You may opt to use, copy, modify, merge, publish, distribute and/or sell
 * copies of the Software, and permit persons to whom the Software is
 * furnished to do so, under the terms of the COPYING file.
 *
 * This software is distributed on an "AS IS" basis, WITHOUT WARRANTY OF ANY
 * KIND, either express or implied.
 *
 ***************************************************************************/
/* Stream-parse a document using the streaming Expat parser.
 * Written by David Strauss
 *
 * Expat => http://www.libexpat.org/
 *
 * gcc -Wall -I/usr/local/include xmlstream.c -lcurl -lexpat -o xmlstream
 *

#define d2r ((22/7.0)/180.0)
#define r2d (180.0/(22/7.0))
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include <expat.h>
#include <curl/curl.h>
#include <openssl/ssl.h>

#include <math.h>

#define pi 3.14159265358979323846
#define CAMERA_FOV 45
#define NUM_RESULTS_IN_FOV 15
#define WINDOW_Xmin 20
#define WINDOW_Xmax 980
#define WINDOW_Ymin 50
#define WINDOW_Ymax 950

double myLatitude;
double myLongitude;
int radius;
typedef struct ResturantStruct {
  char name[50];
  char address[100];
  double lat;
  double lng;
  int distance;
  int angle;
  int imaginaryAngle;
}ResturantStruct;

typedef struct FOVStruct {
  char *name;
  char *address;
  int x;
  int y;
}FOVStruct;

typedef struct MemoryStruct {
  char *memory;
  size_t size;
}MemoryStruct;

typedef struct ParserStruct {
  int ok;
  size_t tags;
  size_t depth;
  struct MemoryStruct characters;
  struct ResturantStruct resturants[100];
  struct FOVStruct FOV[NUM_RESULTS_IN_FOV+1];
  int iName;
  int iAddress;
  int iLat;
  int iLng;
  int angleFromAbsoluteNorth;
}ParserStruct;

double degree2radian(double deg) 
{
  return (deg * pi / 180);
}

double radian2degree(double rad) 
{
  return (rad * 180 / pi);
}

double AngleFromCoordinates(double lat1, double lng1, double lat2, double lng2)
{
  double dlng=(lng2-lng1);
  double x,y,brng;
  y=sin(dlng)*cos(lat2);
  x=(cos(lat1)*sin(lat2))-(sin(lat1)*cos(lat2)*cos(dlng));
  brng=atan2(y,x);
  brng=radian2degree(brng);
  brng=(((int)brng)+360)%360;
  brng=360-brng;
  return brng;
}

double DistanceFromCoordinates(double lat1, double lon1, double lat2, double lon2, char unit)
{
    double rlat1 = (pi*lat1)/180;
    double rlat2 = (pi*lat2)/180;
    double theta = lon1 - lon2;
    double rtheta = pi*theta/180;
    double dist = sin(rlat1) * sin(rlat2) + cos(rlat1) * cos(rlat2) * cos(rtheta);
    dist = acos(dist);
    dist = dist*180/pi;
    dist = dist*60*1.1515;

    switch (unit)
    {
        case 'K': //Kilometers -> default
            return dist * 1.609344;
        case 'N': //Nautical Miles 
            return dist * 0.8684;
        case 'M': //Miles
            return dist;
    }
    return dist;
}

static void startElement(void *userData, const XML_Char *name, const XML_Char **atts)
{
  struct ParserStruct *state = (struct ParserStruct *) userData;
  state->tags++;
  state->depth++;
  /* Get a clean slate for reading in character data. */
  free(state->characters.memory);
  state->characters.memory = NULL;
  state->characters.size = 0;
}

static void characterDataHandler(void *userData, const XML_Char *s, int len)
{
  struct ParserStruct *state = (struct ParserStruct *) userData;
  struct MemoryStruct *mem = &state->characters;
//struct ParserStruct *state = (struct ParserStruct *) userData;
  //state->depth--;
 // printf("%5lu   %10lu   %s\n", state->depth, s, name);
  mem->memory = realloc(mem->memory, mem->size + len + 1);
  if(mem->memory == NULL) {
    /* Out of memory. */
    fprintf(stderr, "Not enough memory (realloc returned NULL).\n");
    state->ok = 0;
    return;
  }
  memcpy(&(mem->memory[mem->size]), s, len);
  mem->size += len;
  mem->memory[mem->size] = 0;
}

static void endElement(void *userData, const XML_Char *name)
{
  struct ParserStruct *state = (struct ParserStruct *) userData;
  state->depth--;
  //printf("%5lu   %10lu   %s   %s\n", state->depth, state->characters.size, state->characters.memory, name);
  if (state->depth==2 && (strcmp(name,"name")==0)){
    sprintf(state->resturants[state->iName].name,"%s",state->characters.memory);
    state->iName++;
  }
  if (state->depth==2 && (strcmp(name,"vicinity")==0)){
    sprintf(state->resturants[state->iAddress].address,"%s",state->characters.memory);
    state->iAddress++;
  }
  if (state->depth==4 && (strcmp(name,"lat")==0)){
    sscanf(state->characters.memory, "%lf", &state->resturants[state->iLat].lat);
    state->iLat++;
  }
  if (state->depth==4 && (strcmp(name,"lng")==0)){
    sscanf(state->characters.memory, "%lf", &state->resturants[state->iLng].lng);
    state->iLng++;
  }
}

static size_t parseStreamCallback(void *contents, size_t length, size_t nmemb, void *userp)
{
  XML_Parser parser = (XML_Parser) userp;
  size_t real_size = length * nmemb;
  struct ParserStruct *state = (struct ParserStruct *) XML_GetUserData(parser);
  /* Only parse if we're not already in a failure state. */
  if (state->ok && XML_Parse(parser, contents, real_size, 0) == 0) {
    int error_code = XML_GetErrorCode(parser);
    fprintf(stderr, "Parsing response buffer of length %lu failed with error code %d (%s).\n",
            real_size, error_code, XML_ErrorString(error_code));
    state->ok = 0;
  }
  return real_size;
}

long map(long x, long in_min, long in_max, long out_min, long out_max)
{
  if ((in_max - in_min) > (out_max - out_min)) {
    return (x - in_min) * (out_max - out_min+1) / (in_max - in_min+1) + out_min;
  }
  else
  {
    return (x - in_min) * (out_max - out_min) / (in_max - in_min) + out_min;
  }
}

int main(void)
{
  radius=500;
  myLatitude=23.7489959;
  myLongitude=90.3917064;
  char jsonURL[250];
  sprintf(jsonURL,"https://maps.googleapis.com/maps/api/place/nearbysearch/xml?types=restaurant&radius=%d&location=%lf,%lf&sensor=true&key=AIzaSyDHR9lSsc7jB8VtYuj6NuaK6QcspfFUnZQ",radius, myLatitude, myLongitude);
  CURL *curl_handle;
  CURLcode res;
  XML_Parser parser;
  struct ParserStruct state;  
  state.iName=0;
  state.iAddress=0;
  state.iLat=0;
  state.iLng=0;
  /* Initialize the state structure for parsing. */
  memset(&state, 0, sizeof(struct ParserStruct));
  state.ok = 1;
  SSL_library_init();
  /* Initialize a namespace-aware parser. */
  parser = XML_ParserCreateNS(NULL, '\0');
  XML_SetUserData(parser, &state);
  XML_SetElementHandler(parser, startElement, endElement);
  XML_SetCharacterDataHandler(parser, characterDataHandler);
  /* Initialize a libcurl handle. */
  curl_global_init(CURL_GLOBAL_ALL ^ CURL_GLOBAL_SSL);
  curl_handle = curl_easy_init();
  curl_easy_setopt(curl_handle, CURLOPT_URL, jsonURL);
  curl_easy_setopt(curl_handle, CURLOPT_WRITEFUNCTION, parseStreamCallback);
  curl_easy_setopt(curl_handle, CURLOPT_WRITEDATA, (void *)parser);

  printf("Depth   Characters   Data   Closing Tag\n");

  /* Perform the request and any follow-up parsing. */
  res = curl_easy_perform(curl_handle);
  if(res != CURLE_OK) {
    fprintf(stderr, "curl_easy_perform() failed: %s\n",
    curl_easy_strerror(res));
  }
  else if (state.ok) {
    /* Expat requires one final call to finalize parsing. */
    if (XML_Parse(parser, NULL, 0, 1) == 0) {
      int error_code = XML_GetErrorCode(parser);
      fprintf(stderr, "Finalizing parsing failed with error code %d (%s).\n",
      error_code, XML_ErrorString(error_code));
    }
    else {
      printf("                     --------------\n");
      printf("                     %lu tags total\n", state.tags);
    }
  }

  int i;/*
  for(i=0;i<=state.iName;i++){
    printf("%s\n",state.resturants[i].name);
  }
  for(i=0;i<=state.iAddress;i++){
    printf("%s\n",state.resturants[i].address);
  }
  for(i=0;i<=state.iLat;i++){
    printf("%lf\n",state.resturants[i].lat);
  }
  for(i=0;i<=state.iLng;i++){
    printf("%lf\n",state.resturants[i].lng);
  }
  */
  //to calculate distance of the resturants
  for(i=0;i<=state.iLat;i++){
    state.resturants[i].distance=DistanceFromCoordinates(myLatitude, myLongitude, state.resturants[i].lat, state.resturants[i].lng, 'K')*1000;
  }
  //to calculate real angle of the resturants
  printf("\n\nrealAngle  imaginaryAngle   Name\n");
  for(i=0;i<=state.iLat;i++){
    state.resturants[i].angle=AngleFromCoordinates(myLatitude,myLongitude, state.resturants[i].lat, state.resturants[i].lng);
    if (state.resturants[i].angle < CAMERA_FOV){//angle<FOV
      state.resturants[i].imaginaryAngle=360+state.resturants[i].angle;
    }
    else if (state.resturants[i].angle>(360-CAMERA_FOV)){//angle>360-FOV
      state.resturants[i].imaginaryAngle=state.resturants[i].angle-360;
    }
    else{
      state.resturants[i].imaginaryAngle=1000; //it will be outside from our search
    }
    printf("<%d\t%d>\t\t\t%s\n", state.resturants[i].angle, state.resturants[i].imaginaryAngle, state.resturants[i].name);
  }
  //to calculate imaginary angle of the resturants
  state.angleFromAbsoluteNorth=18;
  //initialize variables
  int minAngle, maxAngle, FOVidx=0;
  minAngle=state.angleFromAbsoluteNorth - (CAMERA_FOV/2);
  maxAngle=state.angleFromAbsoluteNorth + (CAMERA_FOV/2);
  printf("\n\nangleFromAbsoluteNorth:%d\tminAngle:%d\tmaxAngle:%d\nInside FOV:\nX\tY\tName\n",state.angleFromAbsoluteNorth,minAngle,maxAngle);
  //fill up our list with data inside fov
  for(i=0;i<=state.iLat;i++){
    if (FOVidx<(NUM_RESULTS_IN_FOV)){//don't add more results than max limit
      if ((state.resturants[i].angle > minAngle) && (state.resturants[i].angle < maxAngle) ){//real angle is  inside fov
        state.FOV[FOVidx].name=state.resturants[i].name;
        state.FOV[FOVidx].address=state.resturants[i].address;
        state.FOV[FOVidx].x=map(state.resturants[i].angle, minAngle, maxAngle, WINDOW_Xmin, WINDOW_Xmax);
        state.FOV[FOVidx].y=map(state.resturants[i].distance, 0, radius, WINDOW_Ymin, WINDOW_Ymax);
        FOVidx++;
      }
      else if ((state.resturants[i].imaginaryAngle > minAngle) && (state.resturants[i].imaginaryAngle < maxAngle) ){//imaginary angle is  inside fov
        state.FOV[FOVidx].name=state.resturants[i].name;
        state.FOV[FOVidx].address=state.resturants[i].address;
        state.FOV[FOVidx].x=map(state.resturants[i].imaginaryAngle,minAngle, maxAngle, WINDOW_Xmin, WINDOW_Xmax);
        state.FOV[FOVidx].y=map(state.resturants[i].distance, 0, radius, WINDOW_Ymin, WINDOW_Ymax);
        FOVidx++;
      }
    }
  }
  //print the data inside fov
  for(i=0; i<FOVidx;i++){
    printf("[%d  %d]\t%s\n", state.FOV[i].x, state.FOV[i].y, state.FOV[i].name);
  }
  
  /* Clean up. */
  free(state.characters.memory);
  XML_ParserFree(parser);
  curl_easy_cleanup(curl_handle);
  curl_global_cleanup();
  //delete state;
  return 0;
}
