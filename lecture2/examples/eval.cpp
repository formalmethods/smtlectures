#include <iostream>
#include <cstdio>

int main ( void )
{
  unsigned a = 0xFFFF0000;
  unsigned b = 0x0000FFFF;

  printf( "a + b   : %8X\n", a + b );
  printf( "a * b   : %8X\n", a * b );
  printf( "a AND b : %8X\n", a & b );
  printf( "a OR b  : %8X\n", a | b );

  return 0;
}
