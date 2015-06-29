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

struct ResturantStruct {
  char name[50];
  char address[100];
  char lat[12];
  char lng[12];
  char angle[20];
}ResturantStruct;

struct MemoryStruct {
  char *memory;
  size_t size;
}MemoryStruct;

struct ParserStruct {
  int ok;
  size_t tags;
  size_t depth;
  struct MemoryStruct characters;
  struct ResturantStruct resturants[100];
  int iName;
  int iAddress;
  int iLat;
  int iLng;
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
  printf("%5lu   %10lu   %s   %s\n", state->depth, state->characters.size, state->characters.memory, name);
  if (state->depth==2 && (strcmp(name,"name")==0)){
    sprintf(state->resturants[state->iName].name,"%s",state->characters.memory);
    state->iName++;
  }
  if (state->depth==2 && (strcmp(name,"vicinity")==0)){
    sprintf(state->resturants[state->iAddress].address,"%s",state->characters.memory);
    state->iAddress++;
  }
  if (state->depth==4 && (strcmp(name,"lat")==0)){
    sprintf(state->resturants[state->iLat].lat,"%s",state->characters.memory);
    state->iLat++;
  }
  if (state->depth==4 && (strcmp(name,"lng")==0)){
    sprintf(state->resturants[state->iLng].lng,"%s",state->characters.memory);
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

int main(void)
{
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
  curl_easy_setopt(curl_handle, CURLOPT_URL, "https://maps.googleapis.com/maps/api/place/nearbysearch/xml?types=restaurant&radius=500&location=23.7489959,90.3917064&sensor=true&key=AIzaSyDHR9lSsc7jB8VtYuj6NuaK6QcspfFUnZQ");
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

  double Dlat, Dlng;
  int i;
  for(i=0;i<=state.iName;i++){
    printf("%s\n",state.resturants[i].name);
  }
  for(i=0;i<=state.iAddress;i++){
    printf("%s\n",state.resturants[i].address);
  }
  for(i=0;i<=state.iLat;i++){
    printf("%s\n",state.resturants[i].lat);
  }
  for(i=0;i<=state.iLng;i++){
    printf("%s\n",state.resturants[i].lng);
  }
  
  for(i=0;i<=state.iLat;i++){
    sscanf(state.resturants[i].lat, "%lf", &Dlat);
    sscanf(state.resturants[i].lng, "%lf", &Dlng);
    sprintf(state.resturants[i].angle,"%lf",AngleFromCoordinates(23.7489959,90.3917064, Dlat, Dlng));
    printf("%s\n",state.resturants[i].angle);
  }

  /* Clean up. */
  free(state.characters.memory);
  XML_ParserFree(parser);
  curl_easy_cleanup(curl_handle);
  curl_global_cleanup();
  //delete state;
  return 0;
}