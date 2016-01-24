
: allot ( length -- ) loop 0 , 1 - dup while drop ;
: rdrop ( | r -- | ) r> r> drop >r ;
: lsh ( n shft -- n )
    >r 0
    loop
        swap 2 * swap
        1 + dup i =
    until
    drop rdrop
;


create map 33 25  * allot
create my-x 0 ,
create my-y 0 ,
create up-stairs-x 0 ,
create up-stairs-y 0 ,
create num-slimes 0 ,
create known-gems 0 ,

create path-valid     0 ,
create path-goal      0 ,
create path-dists     33 25 * allot
create path-prevs     33 25 * allot
create path-heap-idx  33 25 * allot
create path-heap      33 25 * allot
create path-heap-len  0 ,

: cell ( x y -- idx ) 33 * + ;
: to-coords ( idx -- x y ) dup 33 mod swap 33 / ;
: my-cell my-x @ my-y @ cell ;

: read-map ( x y -- contents ) cell map + @ ;

: update-map ( contents x y -- )
    over up-stairs-x @ = over up-stairs-y @ = and if
        ( never update the up-stairs, they're really just a floor )
        drop exit
    then
    over over cell map + @ >r ( read/save existing contents )
    >r >r dup r> r>           ( save the new contents )
    cell map + !              ( update the map itself )
    0 path-valid !            ( invalidate pathfinding )
    dup GEM = r> GEM = xor if ( if a gem changed state )
        GEM = if
            ( added a gem )
            known-gems @ 1 + known-gems !
        else
            ( lost a gem )
            known-gems @ 1 - known-gems !
        then
    else
        ( didn't change, don't care )
        drop
    then
;

: set-dist ( distance cell -- )
    path-dists + !
;
: get-dist ( cell -- distance )
    path-dists + @
;
: set-prev ( previous cell -- )
    path-prevs + !
;
: get-prev ( cell -- previous )
    path-prevs + @
;
: cell2idxmask ( cell -- mask idx )
    dup 32 mod     ( compute bit )
    dup 0 > if
        1 swap lsh
    else
        drop 1
    then
    swap 32 /      ( compute index )
;

: want-gems
    num-slimes @ 0 =
    health 5 <
    or
;

create advancing 0 ,
: ready-to-advance -1 advancing ! ;
: dont-advance-yet 0 advancing ! ;
: one 1 ;
: one-thousand 1000 ;
: inf 1000000 ;
: stairs-dist
    advancing @ if
        1
    else
        1000000
    then
;
: door-dist
    keys 0 > if
        1
    else
        1000000
    then
;
: gem-dist
    want-gems if
        1
    else
        1000000
    then
;
create type-dist
    ' one ,          ( FLOOR )
    ' inf ,          ( WALL )
    ' stairs-dist ,  ( STAIRS )
    ' door-dist ,    ( DOOR )
    ' one ,          ( KEY )
    ' gem-dist ,     ( GEM )
    ' one ,          ( SLIME )
    ' inf ,          ( SPIKES )

: dist-to ( cell -- distance )
    map + @
    dup 255 = if
        drop 1
    else
        type-dist + @ exec
    then
;

: explore-goals ( u -- u-is-goal )
    map + @

    ( low-health mode )
    health 3 < if
        known-gems @ 0 > if
            GEM =
            exit
        then
    then

    ( normal explorer mode )
    dup 255 = swap
    dup GEM = want-gems and swap
    KEY =
    or or if
        -1
    else
        0
    then
;
: advance-goals ( u -- u-is-goal )
    map + @
    dup STAIRS = swap 255 = or if
        -1
    else
        0
    then
;
create goal-func ' explore-goals ,
: start-exploring
    ' explore-goals goal-func !
;
: start-advancing
    ' advance-goals goal-func !
;
: is-goal ( u -- u-is-goal )
    goal-func @ exec
;

: heap-left   ( i -- l ) 2 * 1 + ;
: heap-right  ( i -- r ) 2 * 2 + ;
: heap-parent ( i -- p ) 1 - 2 / ;
: path-heap-swap ( i j -- )
    dup  path-heap + @ >r     ( i j | cell-j )
    over path-heap + @ >r     ( i j | cell-j cell-i )
    dup  i path-heap-idx + !  ( cell-idx[cell-i] = j -> ( i j | cell-j cell-i )
    over j path-heap-idx + !  ( cell-idx[cell-j] = i -> ( i j | cell-j cell-i )
    path-heap + r> swap !     ( i | cell-j )
    path-heap + r> swap !     ( )
;
: min-heapify ( i -- )
    >r i heap-right i heap-left i        ( r l smallest | i )
    over path-heap-len @ < if            ( r l smallest | i )
        over path-heap + @ get-dist
        over path-heap + @ get-dist < if ( r l smallest | i )
            swap
        then
    then
    swap drop                            ( r smallest | i )
    over path-heap-len @ < if            ( r smallest | i )
        over path-heap + @ get-dist
        over path-heap + @ get-dist < if ( r l smallest | i )
            swap
        then
    then
    swap drop      ( smallest | i )
    dup i = not if ( smallest | i )
        dup r> path-heap-swap
        min-heapify
    else
        drop rdrop
    then
;
: delete-min ( -- )
    path-heap-len @ 1 - ( nelems - 1 )
    dup path-heap-len ! ( nelems = nelems - 1 )
    0 path-heap-swap    ( swap first and last elements )
    0 min-heapify       ( fix up the heap )
;
: fix-heap ( i -- )
    loop
        dup 0 = if
            break
        then
        ( i -- )
        dup heap-parent path-heap + @ get-dist  ( i dist[parent[i]] | )
        over path-heap + @ get-dist        ( i dist[parent[i]] dist[i] | )
        > if
            dup dup heap-parent path-heap-swap heap-parent
        else
            break
        then
    again
    min-heapify
;

: build-min-heap ( -- )
    path-heap-len @ 2 /
    loop
        dup 0 < if
            drop exit
        then
        dup min-heapify
        1 -
    again
;

: smallest-distance ( -- u )
    path-heap @
;

create neighbors -33 , 33 , -1 , 1 ,

: reset-paths
    0 loop
        1000000  over set-dist    ( dist[v] := infinity ; )
        -1       over set-prev    ( previous[v] := undefined ; )
        dup dup path-heap     + ! ( arbitrarily push cell #s into heap array )
        dup dup path-heap-idx + ! ( starting with 1-to-1 mapping )

        1 + dup 33 25 * =
    until
    path-heap-len !
    0 my-cell set-dist ( dist[source] := 0 ;)
    build-min-heap
;

: dijkstra ( -- [closest goal node] )
    ( "starting dijkstra" typeln )
    path-valid @ if
        path-goal @ exit
    then
    reset-paths
    ( "paths reset" typeln )
    my-cell >r                   ( | u )
    loop
        ( "u = cell " type i . cr )
        delete-min              ( remove u from Q ; ( | u)
        i get-dist 1000000 = if ( if dist[u] = infinity: ( | u )
            ( "we're screwed!" typeln )
            rdrop -1 >r break    (     break ; ( | )
        then                     ( end if ( | u )
        i is-goal if
            ( "it's a goal!" typeln )
            break
        then

        0 >r                     ( | u n )
        loop                     ( for each neighbor v of u: )
            ( "checking neighbor " type i . cr )
            i neighbors + @      (     find next neighbor direction ( noff | u n )
            j +                  (     calculate neighbor cell      ( v | u n )
            ( "neighbor is cell " type dup . cr )
            dup dist-to          (     calculate dist_between(u, v) ( v dist_between[u][v] | u n )
            j get-dist +         (     alt := dist[u] + dist_between(u, v) ( v alt | u n )
            over >r              (     ( v alt | u n v )
            dup r> get-dist      (     ( v alt alt dist[v] | u n )
            ( "new dist " type over . cr )
            ( "prev best " type dup . cr )
            < if                            (     if alt < dist[v]: ( v alt | u n )
                over set-dist               (         dist[v] := alt ; ( v | u n )
                dup j swap set-prev         (         previous[v] := u ; ( v | u n )
                path-heap-idx + @ fix-heap  (         decrease-key v in Q ; ( | u n )
            else
                drop drop
            then                 (     end if )
            r> 1 + dup >r 4 =    (     next neighbor ( | u n )
        until                    ( end for )
        rdrop rdrop

        smallest-distance >r     ( | new_u )
    again
    r>
    dup path-goal  !
    1   path-valid !
    ( "closest goal is cell " type dup . cr )
;

: walk-back ( closest -- first-step )
    ( "walking-back from " type dup . cr )
    my-cell >r
    loop
        dup get-prev
        ( "came from " type dup . cr )
        dup i = if
            drop
            ( "that's our start point, so our first step is " type dup . cr )
            break
        else
            swap drop
            ( "walking-back from " type dup . cr )
        then
    again
    rdrop
;

: reset-map ( -- )
    map 33 25 * +      ( end address )
    map                ( start address)
    loop
        255 over !     ( mark unseen )
        1 +            ( advance )
        over over =    ( check complete )
    until 
    drop drop          ( discard addresses )
    33 2 / my-x !      ( reset position )
    25 2 / my-y !  
    FLOOR my-x @ my-y @ cell map + ! ( know we started on up-stairs )
    my-x @ up-stairs-x !             ( but don't let that change )
    my-y @ up-stairs-y !             ( since 'look' gives stairs )
    dont-advance-yet start-exploring ( haven't explored enough to advance )
    listen num-slimes !
    0 known-gems !
;

: up    ( x y -- x y ) 1 - ;
: down  ( x y -- x y ) 1 + ;
: left  ( x y -- x y ) swap 1 - swap ;
: right ( x y -- x y ) swap 1 + swap ;

create directions
    ' up ,
    ' down ,
    ' left ,
    ' right ,

: scan-for ( filter -- x y)
    >r   ( save the filter )
    0 >r ( loop index )
    loop
        my-x @ my-y @
        directions i + @ exec
        read-map j exec if
            my-x @ my-y @
            directions i + @ exec
            rdrop rdrop exit
        then

        r> 1 + dup >r 4 =
    until
    rdrop rdrop 0 0
;

: slime? ( contents -- bool ) SLIME = ;
: threat ( -- x y ) ' slime? scan-for ;
: threatened? threat over over + 0 = not ;

: unknown? ( contents -- bool ) 255 = ;
: adjacent-unknown ( -- x y ) ' unknown? scan-for ;
: adjacent-unknown? adjacent-unknown over over + 0 = not ;

: stuff?   ( contents -- bool )
    dup KEY = if
        drop -1 exit
    then
    GEM = want-gems and if
        -1 exit
    then
    0
;
: adjacent-stuff ( -- x y ) ' stuff? scan-for ;
: adjacent-stuff? adjacent-stuff over over + 0 = not ;

: door?   ( contents -- bool ) DOOR = ;
: adjacent-door ( -- x y ) ' door? scan-for ;
: adjacent-door? adjacent-door over over + 0 = not ;

: direction ( x y -- dir )
    dup my-y @ < if
        drop drop N exit
    then
    dup my-y @ > if
        drop drop S exit
    then
    over my-x @ < if
        drop drop W exit
    then
    drop drop E ;

: kill ( x y -- )
    over over >r >r           ( save the location of the slime we're killing )
    direction dup attack look ( attack it and verify it's gone )
    r> r> update-map          ( update the map )
    listen num-slimes !       ( verify the slime count )
;

: examine ( x y -- )
    over over >r >r
    direction look   ( poke about )
    r> r> update-map ( update map )
;

: get-stuff ( x y -- )
    over over >r >r            ( save where it was for updating later )
    direction dup take look    ( pick it up, see what's under it )
    r> r> update-map           ( update the map now )
;

: unlock ( x y -- )
    over over >r >r
    direction dup open look
    r> r> update-map
;

: go-there ( cell -- )
    ( "going to cell " type dup . cr )
    walk-back
    ( "first step cell is " type dup . cr )
    to-coords
    ( "in coords, " type over . dup . cr )
    over over direction
    ( be extra careful if there are still slimes alive )
    num-slimes @ 0 > if
        dup look 
        SLIME = if
            drop >r >r
            SLIME r> r> update-map
            exit
        then
    then

    ( should be clear )
    walk

    over over read-map STAIRS = if
        ( "that was stairs, time to reset" typeln )
        drop drop reset-map
    else
        ( "my old position was " type my-x @ . my-y @ . cr )
        my-y ! my-x !
        ( "my new position is " type my-x @ . my-y @ . cr )
    then
;

: brain ( -- )
    fast
    reset-map
    loop
        threatened? if
            kill
        else drop drop adjacent-unknown? if
            examine
        else drop drop adjacent-stuff? if
            get-stuff
        else drop drop adjacent-door? if
            unlock
        else
            drop drop
            ( advancing @ if
                "calling dijkstra" typeln
            then )
            dijkstra
            ( advancing @ if
                "dijkstra complete: " type dup . cr
            then )
            dup -1 > if
                go-there
                ' inf SPIKES type-dist + !
            else
                advancing @ not if
                    ( "completed level!" typeln )
                    drop ready-to-advance start-advancing
                else
                    "must cross spikes!" typeln
                    ' one-thousand SPIKES type-dist + !
                    drop
                then
                0 path-valid !
            then
        then then then then
    again
;

