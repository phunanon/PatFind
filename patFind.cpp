/*Path finding method:
#1  Create a branch at the start position if no other branches are alive
#2  Find closest alive/non-'no-go' (and therefore dead) branch to the destination, if flagged to do so
#3  Check if the branch is at the destination (or we've timed out)
    - If we have a path, optimise it by going through the coords, and checking around each one to see if there is a higher valued path point, then skipping to it
#4  Aim the direction to go in (on each axis either no-move, N, E, S, W)
#5  Try going towards the destination
#6  If both axis could not be moved into, move the original branch one opposite direction, and a new branch, the other. Mark position of split 'no-go.' Flag that we must calculate new closest.
#7  If one axis does not need to be moved on, and the not-no-move direction cannot be moved on, the original branch should go one
          direction of the perpendicular axis, and a new branch, and the other. Mark position of split 'no-go.' Flag that we must calculate new closest.
    - If both new branches cannot be created, go backwards on the not-no-move aim. Mark position backed away from as 'no-go'
    - If that cannot be created, kill the branch again

6 illustration

     @
   #
   +#

7 illustration

  +#  @
*/

#include <iostream> //For output to the terminal
#include <stdio.h> //For output to the terminal: getchar
#include <string> //For use of strings
#include <thread> //For threads, and sleeping
#include <chrono> //For thread sleeping
#include <time.h> //For time keeping
#include <cmath> //For math functions
#include "keypresses.c" //For detecting keypresses: kbhit(), pressedCh

using namespace std;
typedef unsigned char byte;
typedef unsigned int uint;

//===================================
//For optimisation/approx/mathematical code
//===================================
uint g_seed = time(NULL);
inline uint frand()
{ 
  g_seed = (214013 * g_seed + 2531011); 
  return (g_seed >> 16) & 0x7FFF; 
}

union
{
    int tmp;
    float f;
} u;
inline float sqrt_approx(float z)
{
    u.f = z;
    u.tmp -= 1 << 23; /* Subtract 2^m. */
    u.tmp >>= 1; /* Divide by 2. */
    u.tmp += 1 << 29; /* Add ((b + 1) / 2) * 2^m. */
    return u.f;
}

inline float euclideanDistance(int y1, int x1, int y2, int x2) //Calculate the distance between two points, as the crow flies
{
    return sqrt_approx(pow((x2 - x1), 2) + pow((y2 - y1), 2));
}
//===================================

uint y, x, ylen, xlen;
unsigned long i, i2, ilen, i2len;
bool run = true;
bool pfind = false;
bool haveRun = false;
unsigned long startTime = time(NULL);
unsigned long thisTime = time(NULL);
bool timeout = false;

const uint BRANCHMAX = 1024;
const uint HISTMAX = 2048;
const byte OPTIMISE = 32; //Level of path optimisation
const byte DEADTIMEOUT = 16;

const uint boardW = 140;
const uint boardH = 40;
const uint boardWh = boardW / 2;
const uint boardHh = boardH / 2;
bool board[boardH][boardW];
bool bShad[boardH][boardW];
bool bBeen[boardH][boardW];
bool grave[boardH][boardW];
uint foundP[boardH][boardW], pathLen = 0, origPathLen = 0;
bool* look;

uint cursory = boardHh;
uint cursorx = boardWh;
int starty = -1;
int startx = -1;
int findy = -1;
int findx = -1;
bool showcase = false;

class Branch
{
  public:
    uint y;
    uint x;
    uint yhist[HISTMAX];
    uint xhist[HISTMAX];
    uint h; //History count
    bool successful;
    bool dead;
    bool inited;
    void recHist(bool);
    void move(char, char, bool);
    void kill();
    void resurrect();

  Branch();
  Branch(uint, uint, uint[HISTMAX], uint[HISTMAX], uint);
};

Branch::Branch(){}

Branch::Branch(uint Y, uint X, uint Yhist[HISTMAX], uint Xhist[HISTMAX], uint H)
{
    y = Y;
    x = X;
    for (i = 0; i < HISTMAX; i++) //Copy history array passed
    {
        yhist[i] = Yhist[i];
        xhist[i] = Xhist[i];
    }
    h = H;
    move(0, 0, false); //Set in bShad
    dead = false;
    inited = true;
}

void Branch::recHist(bool overwrite)
{
    if (overwrite) { h--; }
    yhist[h] = y;
    xhist[h] = x;
    h++;
}

void Branch::move(char yd, char xd, bool overHist = false)
{
  //Set shadows on the board
    bShad[y][x] = false;
    y += yd;
    x += xd;
    bShad[y][x] = true;
  //Record history
    recHist(overHist);
    bBeen[y][x] = true;
    if ((findy < y && yd == -1) || (findy > y && yd == 1) || (findx < x && xd == -1) || (findx > x && xd == 1)) { successful = true; }
}

void Branch::kill()
{
    dead = grave[y][x] = true;
}

void Branch::resurrect()
{
    dead = grave[y][x] = false;
}


Branch* branch[BRANCHMAX];
uint branches = 0;
uint aliveBs = 0;
uint deadBStreak = 0;
uint b = 0;
Branch* br;
bool nogo[boardH][boardW];

Branch* newBranch(uint y, uint x, Branch* b)
{
    Branch* B;
    if (!b->inited) //Are we working as an initial branch (with no history?)
    {
        uint yhist[HISTMAX] = {};
        uint xhist[HISTMAX] = {};
        B = new Branch(starty, startx, yhist, xhist, 0);
    } else {
        B = new Branch(y, x, b->yhist, b->xhist, b->h);
    }
    if (!aliveBs) { deadBStreak++; } else { deadBStreak = 0; }
    if (branches >= BRANCHMAX || deadBStreak == DEADTIMEOUT) //Time out (Have we: run out of branch space; been creating initial branches rather a lot)?
    {
        timeout = true;
    } else {
        branch[branches] = B;
        branches++;
    }
    aliveBs++;
    return B;
}

bool mayMove(uint Y, uint X)
{
    if (Y < 0) { return false; }
    if (Y > boardH - 1) { return false; }
    if (X < 0) { return false; }
    if (X > boardW - 1) { return false; }
    if (board[Y][X]) { nogo[Y][X] = true; return false; }
    if (nogo[Y][X]) { return false; }
    return true;
}

bool adjacentTo(uint Y, uint X, uint maybeY, uint maybeX)
{
    if (Y - 1 >= 0)   { if (maybeY == Y - 1 && maybeX == X) { return true; } } //Is North of us?
    if (X + 1 < boardW) { if (maybeY == Y && maybeX == X + 1) { return true; } } //Is East of us?
    if (Y + 1 < boardH) { if (maybeY == Y + 1 && maybeX == X) { return true; } } //Is South of us?
    if (X - 1 >= 0)   { if (maybeY == Y && maybeX == X - 1) { return true; } } //Is West of us?
    if (Y == maybeY && X == maybeX) { return true; } //Are we on top of that position?
    return false; //Nope!
}


void clearScreen() { std::cout << "\033[2J\033[1;1H"; }

string buffer;
string buff;
void display()
{
    buffer = "";
    clearScreen();
    for (y = 0; y < boardH; y++)
    {
        for (x = 0; x < boardW; x++)
        {
            buff = "\033[0;30;47m ";
            if (board[y][x])
            {
                buff = "\033[0;30;47m#"; //Block
            }
            if (bBeen[y][x]) //Branch been
            {
                buff = buff.substr(buff.length() - 1, buff.length());
                buff = "\033[37;46m" + buff;
            }
            if (nogo[y][x]) //Nogo
            {
                buff = buff.substr(buff.length() - 1, buff.length());
                buff = "\033[37;41m" + buff;
            }
            if (bShad[y][x]) //Branch
            {
                if (!grave[y][x])
                {
                    buff = "\033[0;30;42m+";
                } else {
                    buff = "\033[0;30;43m+";
                }
            }
            if (foundP[y][x]) //Found path
            {
                buff = buff.substr(buff.length() - 1, buff.length());
                buff = "\033[37;44m" + buff;
            }
            if (y == starty && x == startx) //Start
            {
                buff = "\033[0;30;45m@";
            }
            if (y == findy && x == findx) //Find
            {
                buff = "\033[0;30;42m@";
            }
            if (y == cursory && x == cursorx) //Cursor
            {
                buff = buff.substr(buff.length() - 1, buff.length());
                buff = "\033[37;40m" + buff;
            }
            buffer += buff;
        }
        buffer += "\033[0m\n";
    }
    buffer += std::to_string(cursorx) + ", " + std::to_string(cursory);
    if (pfind || haveRun || showcase)
    {
        if (pfind)
        {
            if (!showcase)
            {
                buffer += "  FINDING  ";
            } else {
                buffer += "  SHOWCASING  ";
            }
        } else {
            buffer += "  HAVE RUN (";
            if (timeout) { buffer += "TIMEOUT"; } else { buffer += "SUCCESS/PAUSE"; }
            buffer += ")  ";
        }
        buffer += "len: " + to_string(pathLen) + " (opti'd by " + to_string(origPathLen - pathLen) +  ")  ";
        buffer += to_string(thisTime - startTime) + "s";
        buffer += "  branches: " + to_string(branches) + "  alive: " + to_string(aliveBs);
    }
    cout << buffer << endl;
}

bool inputted;
string getInput()
{
    string toReturn = "";
    while (!inputted)
    {
        while (kbhit())
        {
            pressedCh = getchar(); //Get the key
            cout << pressedCh; //Echo it to the user
            fflush(stdout);
            if (pressedCh == '\n')
            {
                inputted = true;
            } else {
                toReturn += pressedCh;
            }
        }
        this_thread::sleep_for(std::chrono::milliseconds(64));
    }
    inputted = false;
    return toReturn;
}

void cleanUp()
{
    haveRun = false;
    timeout = false;
    deadBStreak = 0;
    //for (b = 0; b < branches; b++) { delete branch[b]; } //Go through each branch, and delete
    memset(branch, 0, sizeof(branch)); //Remove all existing branch pointers
    branches = 0;
    aliveBs = 0;
    for (y = 0; y < boardH; y++) //Clear arrays
    {
        for (x = 0; x < boardW; x++)
        {
            nogo[y][x] = false;
            bShad[y][x] = false;
            bBeen[y][x] = false;
            foundP[y][x] = 0;
        }
    }
}

void randBoard(char mode)
{
    for (y = 0; y < boardH; y++)
    {
        for (x = 0; x < boardW; x++)
        {
            switch (mode)
            {
                case 'r':
                    if (!(frand() % 4)) { board[y][x] = 1; }
                     else { board[y][x] = 0; }
                    break;
                case 'l':
                    if (!(frand() % 8)) { board[y][x] = 1; }
                     else { board[y][x] = 0; }
                    break;
                case 's':
                    if (!(y % ((frand() % 2) + 8)) != !(x % ((frand() % 2) + 16))) { board[y][x] = 1; }
                     else { board[y][x] = 0; }
                    break;
                case 'm':
                    board[y][x] = (!((y % 2) + (x % 2)) ? 1 : 0);
                    if (frand() % 10 > 5 && (y % 2 == 0 || x % 2 == 0)) { board[y][x] = 1; }
                    break;
                case 'c':
                    board[y][x] = 0;
                    break;
            }
        }
    }
    if (mode == 'c')
    {
        float step = 0.1f;
        float angle;
        for (i = 0; i < 16; i++)
        {
            angle = 0.0f;
            int size = (frand() % 20) + 10, offY, offX;
            y = frand() % boardH;
            x = frand() % boardW;
            while (angle < 6.28f)
            {
              //Calculate the x and y of this part of the circle
                offY = (size * (float)cos(angle)) / 2;
                offX = size * (float)sin(angle);
              //Place obstacle
                if (y + offY < boardH && x + offX < boardW) { board[y + offY][x + offX] = 1; }
                angle += step;
            }
        }
    }
    do
    {
        starty = frand() % boardH;
        startx = frand() % boardW;
        findy = frand() % boardH;
        findx = frand() % boardW;
    } while (euclideanDistance(starty, startx, findy, findx) < boardW / 2);
}

bool moved, success, calcClosest;
uint prevY, prevX, ed, minEd, useB;
byte aimY, aimX, movedY, movedX;

int main()
{
  //Load shite to listen to pressed keys
    loadKeyListen();
    cout << "Patfind, by Patrick Bowen [phunanon] 2016.\nControls: .ueo NESW move, a obstacle, h set start, t set finish, r randomly create, c clear, [space] begin find, [enter] begin showcase\nPress any key to continue.";
    getchar();

    while (run)
    {
        display();

        while (kbhit())
        {
            look = &board[cursory][cursorx];
            pressedCh = getchar(); //Get the key
            switch (pressedCh)
            {
                case '.': //Up
                    if (cursory > 0) { cursory--; }
                    break;
                case 'u': //Right
                    if (cursorx + 1 < boardW) { cursorx++; }
                    break;
                case 'e': //Down
                    if (cursory + 1 < boardH) { cursory++; }
                    break;
                case 'o': //Left
                    if (cursorx > 0) { cursorx--; }
                    break;
                case 'a': //Toggle block
                    *look = !*look;
                    break;
                case 'h': //Set start
                    starty = cursory;
                    startx = cursorx;
                    break;
                case 't': //Set find
                    findy = cursory;
                    findx = cursorx;
                    break;
                case '\n': //Toggle showcase
                    showcase = !showcase;
                    if (showcase) { cleanUp(); randBoard('r'); }
                    pfind = showcase;
                    break;
                case ' ': //Toggle pathfind
                    if (haveRun) //Have we already run?
                    {
                        pfind = false;
                      //Cleanup
                        cleanUp();
                    } else {
                        if (starty + startx >= 0 && findy + findx >= 0)
                        {
                            pfind = !pfind;
                            if (pfind)
                            {
                                startTime = thisTime = time(NULL);
                                haveRun = true;
                            }
                        }
                    }
                    break;
                case 'r': //Make random
                {
                    cleanUp();
                    cout << "Dense (r) or square (s) or light (l) or maze (m) or circles (c)?" << endl;
                    while (!kbhit()) { this_thread::sleep_for(chrono::milliseconds(50)); }
                    char mode = getchar();
                    randBoard(mode);
                }
                    break;
                case 'c': //Clear
                    memset(board, 0, sizeof(board));
                    starty = startx = findy = findx = -1;
                    break;
                case 'q': //Quit
                    std::cout << "Quit.\033[0m" << std::endl;
                    run = false;
                    break;
            }
        }





        if (pfind)
        {
            success = false;
            minEd = boardW * boardH;
//#1    Create a branch at the start position if no other branches are alive
            if (aliveBs == 0) //Create an initial/retry branch
            {
                newBranch(starty, startx, new Branch());
            }
            aliveBs = 0;
//#2    Find closest branch to the destination, if flagged to do so
            if (calcClosest)
            {
                for (b = 0; b < branches; b++) //Go through each branch, and find the closest alive one
                {
                    br = branch[b];
                    if (nogo[br->y][br->x]) { br->kill(); continue; }
                    if (!br->dead)
                    {
                        ed = euclideanDistance(br->y, br->x, findy, findx);
                        if (ed < minEd) { minEd = ed; useB = b; }
                    }
                    aliveBs++;
                }
            }
            br = branch[useB];
            pathLen = origPathLen = br->h;
//#3    Is this branch at the find (or timed out)?
            if (adjacentTo(br->y, br->x, findy, findx) || timeout) //DID WE FIND IT?... or did we timeout?
            {
                pfind = false;
                pathLen = 0;
                origPathLen = br->h;
              //Render found path from history
                if (!timeout)
                {
                    ilen = br->h;
                    uint ignoreUntil;
                    for (i = 0; i < ilen; i++)
                    {
                        if (!ignoreUntil || i == ignoreUntil)
                        {
                            ignoreUntil = 0;
                            y = br->yhist[i];
                            x = br->xhist[i];
                            foundP[y][x] = i;
                            pathLen++;
                          //Path optimisation
                            if (i < ilen - OPTIMISE)
                            {
                                i2len = i;
                                for (i2 = i + OPTIMISE; i2 > i2len; i2--)
                                {
                                    if (adjacentTo(br->yhist[i2], br->xhist[i2], y, x))
                                    {
                                        ignoreUntil = i2;
                                        break;
                                    }
                                }
                            }
                            display();
                            this_thread::sleep_for(std::chrono::milliseconds(4));
                        }
                    }
                }
                if (showcase) //Are we showcasing?
                {
                    display();
                    pfind = true;
                    cleanUp();
                    char mode = 'r';
                    if (!(frand() % 5)) { mode = 'l'; }
                     else if (!(frand() % 4)) { mode = 's'; }
                     else if (!(frand() % 3)) { mode = 'm'; }
                     else if (!(frand() % 2)) { mode = 'c'; } 
                    randBoard(mode);
                    this_thread::sleep_for(std::chrono::milliseconds(1280));
                    startTime = thisTime = time(NULL); //For showcasing
                }
                continue;
            }
//#4    Aim the direction to go in
            if (br->y == findy) { aimY = 0; } //No-move Y
            if (br->x == findx) { aimX = 0; } //No-move X
            if (br->y > findy) { aimY = 1; } //Move North
            if (br->x < findx) { aimX = 2; } //Move East
            if (br->y < findy) { aimY = 3; } //Move South
            if (br->x > findx) { aimX = 4; } //Move West
//#5    Try going towards the destination
            prevY = br->y;
            prevX = br->x;
            br->successful = false;
            if (aimY == 1) //North
            {
                if (mayMove(br->y - 1, br->x))
                {
                    br->move(-1, 0);
                }
            }
            if (aimX == 2) //East
            {
                if (mayMove(br->y, br->x + 1))
                {
                    br->move(0, 1);
                }
            }
            if (aimY == 3) //South
            {
                if (mayMove(br->y + 1, br->x))
                {
                    br->move(1, 0);
                }
            }
            if (aimX == 4) //West
            {
                if (mayMove(br->y, br->x - 1))
                {
                    br->move(0, -1);
                }
            }

            if (br->successful) { success = true; } //State that there was success

//#6    Check how we moved 1
        //If both axis could not be moved into, move the original branch one opposite direction, and a new branch, the other
            if (aimX != 0 && prevX == br->x && aimY != 0 && prevY == br->y)
            {
                calcClosest = true;
                moved = false;
              //Mark here as a nogo
                nogo[br->y][br->x] = true;

                prevY = br->y;
                prevX = br->x;

              //Make the original branch go in the opposing X direction
                if (aimX == 4) //To now move East
                {
                    if (mayMove(br->y, br->x + 1))
                    {
                        br->move(0, 1);
                        moved = true;
                    }
                } else { //To now move West
                	if (mayMove(br->y, br->x - 1))
                    {
                        br->move(0, -1);
                        moved = true;
                    }
                }
              //If that move didn't work, we're dead!
                if (!moved)
                {
                    br->kill();
                }
              //Make a new branch go in the opposing Y direction
                moved = false;
                Branch* b2 = newBranch(prevY, prevX, br);
                if (aimY == 1) //To now move South
                {
                    if (mayMove(b2->y + 1, b2->x))
                    {
                        b2->move(1, 0);
                        moved = true;
                    }
                } else { //To now move North
                	if (mayMove(b2->y - 1, b2->x))
                    {
                        b2->move(-1, 0);
                        moved = true;
                    }
                }
                if (!moved)
                {
                    b2->kill();
                }
            }
//#7    Check how we moved 2
          //If one axis does not need to be moved on, and the not-no-move direction cannot be moved on, the original branch should go one direction of the perpendicular axis, and a new branch, and the other
            if ((aimY == 0 && aimX != 0 && prevX == br->x) || (aimX == 0 && aimY != 0 && prevY == br->y))
            {
                calcClosest = true;
                moved = false;
              //Mark here as a nogo
                nogo[br->y][br->x] = true;

                prevY = br->y;
                prevX = br->x;

                if (aimX != 0)                      //Tried moving East or West - create a branch North and South
                {
                    if (mayMove(br->y - 1, br->x))  //Can move original branch North?
                    {
                        br->move(-1, 0);
                        moved = true;
                    } else {                        //Kill this branch, otherwise
                        br->kill();
                    }
                  //Create a new branch, to move South
                    Branch* b2 = newBranch(prevY, prevX, br);
                    if (mayMove(b2->y + 1, b2->x))  //Can move new branch South?
                    {
                        b2->move(1, 0);
                        moved = true;
                    } else {                        //Kill this branch, otherwise
                        b2->kill();
                    }
                }

                if (aimY != 0) // Tried moving North or South - create a branch East and West
                {
                    if (mayMove(br->y, br->x + 1))  //Can move original branch East?
                    {
                        br->move(0, 1);
                        moved = true;
                    } else {                        //Kill this branch, otherwise
                        br->kill();
                    }
                  //Create a new branch, to move West
                    Branch* b2 = newBranch(prevY, prevX, br);
                    if (mayMove(b2->y, b2->x - 1))  //Can move new branch West?
                    {
                        b2->move(0, -1);
                        moved = true;
                    } else {                        //Kill this branch, otherwise
                        b2->kill();
                    }
                }
                
                
                if (!moved) //If we didn't manage to move either branch, move back on the no-move axis
                {
                  //Resurrect the original branch
                    br->resurrect();
                  //Move it backwards
                    if (aimX == 0) //Move it backwards on Y
                    {
                        if (mayMove(br->y + (aimY == 1 ? 1 : -1), br->x))
                        {
                            br->move((aimY == 1 ? 1 : -1), 0, true);
                            moved = true;
                        }
                    } else { //Move it backwards on X
                        if (mayMove(br->y, br->x + (aimX == 4 ? 1 : -1)))
                        {
                            br->move(0, (aimX == 4 ? 1 : -1), true);
                            moved = true;
                        }
                    }
                    if (!moved) // If we failed to move, again, kill it again
                    {
                        br->kill();
                    }
                }
            }
            thisTime = time(NULL);
        }
        this_thread::sleep_for(std::chrono::milliseconds(8));
    }

    return 0;
}
