/* projeto_m
 * Author: Ricar
 * Creation date: 06/05/2019
 */
MACHINE
    projeto_m
SEES projeto_m_ctx
VARIABLES
    //Remover depois
    books, price, copies, cart,
    gift_books, history,
    
    //Novos
    users, admins, clients, stores, 
    products, carts, logged
    
INVARIANT
    users <: USER
    & admins <: ADMIN
    & clients <: CLIENT
    & stores <: STORE
    & products <: ADMIN
    & carts : clients --> (products +-> NATURAL1)
    
    
    & books <: BOOK
    & price : books --> NATURAL1
    & copies : books --> NATURAL
    & users <: USER
    & logged : users --> BOOL
    & cart : users --> (books +-> NATURAL1)
    & ! ff . (ff : ran(cart) =>
                ! bb . (bb : dom(ff) => ff(bb) <= copies(bb)))
    & gift_books : seq(books)
    & history : seq(NATURAL1)
INITIALISATION
    admins, clients, stores, products, carts := {},{},{},{},{}
    || books, price, copies := {}, {}, {}
    || users, logged, cart := {}, {}, {}
    || gift_books := []
    || history := []
OPERATIONS
    add_to_stock(bb,pp,cc) =
    PRE
        bb : BOOK & bb /: books
        & pp : NATURAL1 & cc : NATURAL1
    THEN
        books := books \/ {bb}
        || price := price \/ {(bb |-> pp)}
        || copies := copies \/ {(bb |-> cc)}
    END
    ;
    remove_from_stock(bb) =
    PRE
        bb : BOOK & bb : books & copies(bb) = 0
        & bb /: ran(gift_books)
        & bb /: dom(union(ran(cart)))
    THEN
        books := books - {bb}
        || price := price - {(bb |-> price(bb))}
        || copies := {bb} <<| copies
    END
    ;
    buy_copies(bb,cc) =
    PRE
        bb : BOOK & bb : books
        & cc : NATURAL1
    THEN
        copies := copies <+ {(bb |-> copies(bb) + cc)}
    END
    ;
    mark_as_gift(bb) =
    PRE
        bb : BOOK & bb : books & copies(bb) > 0
    THEN
        gift_books := gift_books <- bb
        || copies(bb) := copies(bb)-1
    END
    ;
    unmark_as_gift(bb) =
    PRE
        bb : BOOK & bb : books & bb : ran(gift_books)
    THEN
        ANY
            ii
        WHERE
            ii : dom(gift_books) & gift_books(ii) = bb
        THEN
            gift_books := (gift_books /|\ (ii-1)) ^ (gift_books \|/ ii)
            || copies(bb) := copies(bb)+1
        END
    END
    ;
    add_user(uu) =
    PRE
        uu : USER & uu /: users
    THEN
        users := users \/ {uu}
        || logged := logged \/ {(uu |-> FALSE)}
        || cart := cart \/ {(uu |-> {})}
    END
    ;
    remove_user(uu) =
    PRE
        uu : USER & uu : users
    THEN
        users := users - {uu}
        || logged := {uu} <<| logged
        || cart := {uu} <<| cart
    END
    ;
    login(uu) =
    PRE
        uu : USER & uu : users
        & logged(uu) = FALSE
    THEN
        logged(uu) := TRUE
    END
    ;
    logout(uu) =
    PRE
        uu : USER & uu : users
        & logged(uu) = TRUE
    THEN
        logged(uu) := FALSE
        || cart(uu) := {}
    END
    ;
    add_book_to_cart(uu,bb,cc) =
    PRE
        uu : USER & uu : users & logged(uu) = TRUE
        & bb : BOOK & bb : books & cc : NATURAL1
        & copies(bb) >= cc
        & (cart(uu) /= {} & bb : dom(cart(uu)) => copies(bb) >= cart(uu)(bb) + cc)
    THEN
        IF bb : dom(cart(uu)) THEN
            cart(uu) := cart(uu) <+ {(bb |-> cart(uu)(bb) + cc)}
        ELSE
            cart(uu) := cart(uu) \/ {(bb |-> cc)}
        END
    END
    ;
    update_cart(uu,bb,cc) =
    PRE
        uu : USER & uu : users & logged(uu) = TRUE & cart(uu) /= {}
        & bb : BOOK & bb : books & bb : dom(cart(uu))
        & cc : NATURAL & copies(bb) >= cc
    THEN
        IF cc = 0 THEN
            cart(uu) := {bb} <<| cart(uu)
        ELSE
            cart(uu)(bb) := cc
        END
    END
    ;
    checkout(uu) =
    PRE
        uu : USER & uu : users & logged(uu) = TRUE
        & card(cart(uu)) > 0
        & ! bb . (bb : dom(cart(uu)) => cart(uu)(bb) <= copies(bb))
    THEN
        LET total
        BE total = (SIGMA bb . (bb : dom(cart(uu)) | cart(uu)(bb) * price (bb)))
        IN
            ANY final_total, gift
            WHERE final_total : NATURAL1 & final_total : {total, total/2}
                  & gift : BOOL & (gift = TRUE => size(gift_books) > 0)
            THEN  
               copies := copies <+
                         { bb,cc | bb : BOOK & bb : dom(cart(uu)) & cc : NATURAL
                                   & cc = copies(bb) - cart(uu)(bb) }
               || cart(uu) := {}
               || history := history <- final_total
               || IF gift = TRUE THEN
                   ANY ii
                   WHERE ii : dom(gift_books)
                   THEN gift_books := (gift_books /|\ (ii-1)) ^ (gift_books \|/ ii)
                   END                   
               END
            END
        END           
    END
    ;
    income <-- get_income =
    BEGIN
        income := (SIGMA ii . (ii : dom(history) | history(ii)))    
    END
    ;
    income <-- get_last3_income =
    PRE
        size(history) >= 3
    THEN    
        income := (SIGMA ii . (ii : dom(rev(history) /|\ 3) | rev(history)(ii)))    
    END
END