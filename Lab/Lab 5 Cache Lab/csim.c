/* 20220100 Kihyun Park */

#include "cachelab.h"
#include <stdio.h>
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>

typedef struct //Cache Block
{
    int valid_bit;
    int tag;
    int* block;
    int LRU;
} Line;

Line** Cache; //Cache Memory

int opt = 0;
int help_flag = 0;
int verbose_flag = 0;
int s = 0; //Number of set index bits
int S = 0; //Number of sets
unsigned int E = 0; //Number of lines per set
int b = 0; //Number of block bits
unsigned int B = 0; //Block size
char* t = NULL; //trace file

int hit_count = 0;
int miss_count = 0;
int eviction_count = 0;

void print_helpflag();
void CacheInit();
void DeleteCache();
void TraceInput();
void CacheSimulator(unsigned long int address);

int main(int argc, char* argv[])
{
    //Parse command-line arguments
    while((opt = getopt(argc, argv, "hvs:E:b:t:")) != -1)
    {
        switch(opt)
        {
            case 'h':
                help_flag = 1;
                break;
            case 'v':
                verbose_flag = 1;
                break;
            case 's':
                s = atoi(optarg);
                S = (unsigned)pow(2, s);
                break;
            case 'E':
                E = atoi(optarg);
                break;
            case 'b':
                b = atoi(optarg);
                B = (unsigned)pow(2, b);
                break;
            case 't':
                t = optarg;
                break;
        }
    }

    //Print usage info
    print_helpflag();
    
    //Cache Init
    CacheInit();

    //Tracefile Input
    TraceInput();

    //Delete Cache
    DeleteCache();

    //Print Results
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}

void print_helpflag()
{
    if(help_flag)
    {
        printf("\nUsage: ./csim-ref [-hv] -s <s> -E <E> -b <b> -t <tracefile>\n");
        printf("  -h: Optional help flag that prints usage info\n");
        printf("  -v: Optional verbose flag that displays trace info\n");
        printf("  -s <s>: Number of set index bits (S = 2^s is the number of sets)\n");
        printf("  -E <E>: Associativity (number of lines per set)\n");
        printf("  -b <b>: Number of block bits (B = 2^b is the block size)\n");
        printf("  -t <tracefile>: Name of the valgrind trace to replay\n\n");
    }
    return;
}

void CacheInit()
{
    Cache = (Line**)malloc(sizeof(Line*) * S);
    for(int i = 0; i < S; i++)
    {
        Cache[i] = (Line*)malloc(sizeof(Line) * E);
        for(int j = 0; j < E; j++)
        {
            Cache[i][j].valid_bit = 0;
            Cache[i][j].tag = 0;
            Cache[i][j].block = (int*)malloc(sizeof(int) * B);
            Cache[i][j].LRU = 0;
        }
    }
    return;
}

void DeleteCache()
{
    for(int i = 0; i < S; i++)
    {
        for(int j = 0; j < E; j++)
        {
            free(Cache[i][j].block);
        }
        free(Cache[i]);
    }
    free(Cache);
    return;
}

void TraceInput()
{
    FILE* tracefile;

    char operation = NULL;
    unsigned long int address = 0;
    int size = 0;

    tracefile = fopen(t, "r");
    while(fscanf(tracefile, " %c %lx, %d", &operation, &address, &size) != EOF)
    {
        if(verbose_flag)
        {
            printf("%c %lx,%d", operation, address, size);
        }

        switch(operation)
        {
            case 'L':
                CacheSimulator(address);
                break;
            case 'M':
                CacheSimulator(address);
                CacheSimulator(address);
                break;
            case 'S':
                CacheSimulator(address);
                break;
        }

        if(verbose_flag)
        {
            printf("\n");
        }
    }
    fclose(tracefile);
    return;
}

void CacheSimulator(unsigned long int address)
{
    unsigned long int tag = (address >> (s + b));
    unsigned long int set = ((address >> b) & (S - 1));
    int LRU_num = -1;
    int hit_line = 0;
    int eviction_line = 0;
    int hit_or_not = 0;
    int evict_or_not = 0;

    //Check hits
    for(int i = 0; i < E; i++)
    {
        if(Cache[set][i].valid_bit == 1)
        {
            if(Cache[set][i].tag == tag)
            {
                hit_or_not = 1;
                hit_line = i;
                Cache[set][i].LRU = 0;
                break;
            }
        }
    }
    if(hit_or_not == 1)
    {
        for(int i = 0; i < E; i++)
        {
            if((i != hit_line) && (Cache[set][i].valid_bit == 1))
            {
                Cache[set][i].LRU++;
            }
        }

        hit_count++;
        if(verbose_flag)
        {
            printf(" hit");
            //
            printf("\t\t\t\tSet:%3lx, Tag: %lx", set, tag);
            //
        }
        return;
    }

    //Check misses and evictions
    miss_count++;
    if(verbose_flag)
    {
        printf(" miss");
    }

    for(int i = 0; i < E; i++)
    {
        if(Cache[set][i].valid_bit == 0)
        {
            evict_or_not = -1;
            eviction_line = i;
            break;
        }
        else
        {
            if(Cache[set][i].LRU > LRU_num)
            {
                LRU_num = Cache[set][i].LRU;
                evict_or_not = 1;
                eviction_line = i;
            }
        }
    }

    for(int i = 0; i < E; i++)
    {
        if((i != eviction_line) && (Cache[set][i].valid_bit == 1))
        {
            Cache[set][i].LRU++;
        }
    }

    if(evict_or_not == -1)
    {
        Cache[set][eviction_line].valid_bit = 1;
        Cache[set][eviction_line].tag = tag;
        Cache[set][eviction_line].LRU = 0;
        //
        printf("\t\t\t");
        //
    }
    else if(evict_or_not == 1)
    {
        eviction_count++;
        if(verbose_flag)
        {
            printf(" eviction");
        }
        Cache[set][eviction_line].tag = tag;
        Cache[set][eviction_line].LRU = 0;
    }
    //
    printf("\tSet:%3lx, Tag: %lx", set, tag);
    //
    return;
}