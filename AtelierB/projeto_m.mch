/* projeto_m
 * Author: Ricar
 * Creation date: 06/05/2019
 */
MACHINE
    projeto_m
SEES projeto_m_ctx
    
VARIABLES
    users, admins, 
    products, carts,
    logged,
    
    stores, store_adresses, store_names, store_responsible,
    
    clients, client_residencial_adresses, client_house_adresses, client_names, client_date,
    
    product_description, product_color, product_amount, product_enable, product_image
    
INVARIANT
    users <: USER
    & admins <: users   
    & clients <: users
    & logged : users --> BOOL

    & stores <: STORE
    & products <: PRODUCT
    & carts : clients --> (products +-> INT)
    
    // STORE
    & store_adresses : stores --> ADRESS
    & store_names : stores --> NAME
    & store_responsible : stores --> USER
    
    //STORE
    & client_residencial_adresses : clients --> ADRESS
    & client_house_adresses : clients --> ADRESS
    & client_names : clients --> NAME
    & client_date : clients --> DATE
    
    & product_description: products --> DESCRIPTION
    & product_color: products --> COLOR
    & product_amount: products --> INT
    & product_enable: products --> BOOL
    & product_image: products --> IMAGE

INITIALISATION
    users, admins, logged :=  {},{},{}
    || products, carts := {},{}
    || stores, store_adresses, store_names, store_responsible := {},{},{},{}
    
    || clients, client_residencial_adresses, client_house_adresses := {},{},{}
    || client_names, client_date := {},{}
    
    || product_description, product_color, product_amount := {},{},{}
    || product_enable, product_image := {},{}
    
OPERATIONS
    // LOGIN
    login(uu) =
    PRE
        uu : USER & uu : users & logged(uu) = FALSE
    THEN
        logged(uu) := TRUE
    END
    ;
    logout(uu) =
    PRE
        uu : USER & uu : users & logged(uu) = TRUE
    THEN
        IF uu : clients THEN
            logged(uu) := FALSE
            || carts(uu) := {}
        ELSE
            logged(uu) := FALSE
        END
    END
    ;    
    // STORE (ss=store,  rr== responsible, aa=adress, nn=name, ad=admin)
    add_store(ss, rr, aa, nn, ad) =
    PRE
        (ss : STORE & ss /: stores) 
        & (rr : USER & rr : users)
        & aa : ADRESS
        & nn : NAME
        & ad : admins 
        & logged(ad) = TRUE
    THEN
        stores := stores \/ {ss}
        || store_adresses := store_adresses \/ {(ss |-> aa)}
        || store_names := store_names \/ {(ss |-> nn)}
        || store_responsible := store_responsible \/ {(ss |-> rr)}
    END
    ;    
    remove_store(ss, rr) =
    PRE
        (ss : STORE & ss : stores)
        & (rr : USER & rr : users & rr = store_responsible(ss))
        & rr : admins & logged(rr) = TRUE
    THEN
        stores := stores - {ss}
        || store_adresses := store_adresses - {(ss |-> store_adresses(ss))}
        || store_names := store_names - {(ss |-> store_names(ss))}
        || store_responsible := store_responsible - {(ss |-> store_responsible(ss))}
    END
    ;
    // CLIENT (cc=client, dd=date, aar=residencial adress, aah= house adress, nn=name)
    add_client(cc, dd, aar, aah, nn) =
    PRE
        (cc : USER & cc /: clients & cc /: users) 
        & aar : ADRESS
        & aah : ADRESS
        & nn : NAME
        & dd : DATE
    THEN
        clients := clients \/ {cc}
        || users := users \/ {cc}
        || logged := logged \/ {(cc |-> FALSE)}
        || client_residencial_adresses := client_residencial_adresses \/ {(cc |-> aar)}
        || client_house_adresses := client_house_adresses \/ {(cc |-> aah)}
        || client_names := client_names \/ {(cc |-> nn)}
        || client_date := client_date \/ {(cc |-> dd)}
        || carts := carts \/ {(cc |-> {})}
    END
    ;
    remove_client(cc, aa) =
    PRE
        (cc : USER & cc : clients & cc : users)
        & (aa : USER & aa : admins & aa : users)
        & (logged(cc) = TRUE)
    THEN
        clients := clients - {cc}
        || users := users - {cc}
        || logged := {cc} <<| logged
        || client_residencial_adresses := client_residencial_adresses - {(cc |-> client_residencial_adresses(cc))}
        || client_house_adresses := client_house_adresses - {(cc |-> client_house_adresses(cc))}
        || client_names := client_names - {(cc |-> client_names(cc))}
        || client_date := client_date - {(cc |-> client_date(cc))}
        || carts := {cc} <<| carts
    END
    ;
    // PRODUCT (ss=storage, pp=product, rr=responsible, dd=description, color=color, aa= amount, ee=enable, ii=image)
    add_product(ss, pp, rr, dd, cc, aa, ee, ii) =
    PRE
        ss : STORE & ss : stores 
        & rr : USER & rr : users & store_responsible(ss) = rr & logged(rr) = TRUE
        & (pp : PRODUCT & pp /: products)
        & dd : DESCRIPTION
        & cc : COLOR
        & aa : INT
        & ee : BOOL
        & ii : IMAGE
    THEN
        products := products \/ {pp}
        || product_description := product_description \/ {(pp |-> dd)}
        || product_color := product_color \/ {(pp |-> cc)}
        || product_amount := product_amount \/ {(pp |-> aa)}
        || product_enable := product_enable \/ {(pp |-> ee)}
        || product_image := product_image \/ {(pp |-> ii)}
    END
    ;
    remove_product(ss, pp, rr) =
    PRE
        ss : STORE & ss : stores 
        & rr : USER & rr : users & store_responsible(ss) = rr & logged(rr) = TRUE
        & (pp : PRODUCT & pp : products)
    THEN
        products := products - {pp}
        || product_description := product_description - {(pp |-> product_description(pp))}
        || product_color := product_color - {(pp |-> product_color(pp))}
        || product_amount := product_amount - {(pp |-> product_amount(pp))}
        || product_enable := product_enable - {(pp |-> product_enable(pp))}
        || product_image := product_image - {(pp |-> product_image(pp))}
    END
    ;
    // CARTS ( pp=product, aa=amount, cc=client)
    add_product_to_cart(pp, aa, cc) =
    PRE
        pp : PRODUCT & pp : products 
        & aa : INT
        & cc : USER & cc : clients & logged(cc) = TRUE 
        & carts(cc) /= {} 
        & product_amount(pp) >= aa 
        & product_enable(pp) = TRUE
    THEN
        IF pp : dom(carts(cc)) THEN
            carts(cc) := carts(cc) <+ {(pp |-> carts(cc)(pp) + aa)}
        ELSE
            carts(cc) := carts(cc) \/ {(pp |-> aa)}
        END
    END
    ;    
    remove_product_of_cart(pp, aa, cc) =
    PRE
        pp : PRODUCT & pp : products 
        & aa : INT
        & cc : USER & cc : clients & logged(cc) = TRUE 
        & carts(cc) /= {}
        & pp : dom(carts(cc))
        & carts(cc)(pp) >= aa
        & product_enable(pp) = TRUE
    THEN
        carts(cc) := carts(cc) <+ {(pp |-> carts(cc)(pp) - aa)}
    END
    
END