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
    store_products, store_bought_products,
    
    clients, client_adresses, client_names, client_date,
    client_form_payment,
    clients_product_bought,
    
    product_name,
    product_description, product_color, product_amount, product_enable, 
    product_image, product_category
    
INVARIANT
    users <: USER
    & admins <: users   
    & clients <: users
    & logged : users --> BOOL

    & stores <: STORE
    & products <: PRODUCT
    & carts : clients --> (products +-> INT)
    & clients_product_bought : clients --> (products +-> INT)
    
    // STORE
    & store_adresses : stores --> ADRESS
    & store_names : stores --> NAME
    & store_responsible : stores --> USER
    & store_products : stores --> seq(PRODUCT)
    & store_bought_products : stores --> (products +-> INT)
    
    //CLIENT
    & client_adresses : clients --> seq(ADRESS)
    & client_names : clients --> NAME
    & client_date : clients --> DATE
    & client_form_payment: clients --> seq(FORM_PAYMENT)
    
    //PRODUCT
    & product_name : products --> NAME
    & product_description: products --> DESCRIPTION
    & product_color: products --> COLOR
    & product_amount: products --> INT
    & product_enable: products --> BOOL
    & product_image: products --> IMAGE
    & product_category: products --> PROD_CATEGORY

INITIALISATION
    users, admins, logged :=  {},{},{}
    || products, carts := {},{}
    || stores, store_adresses, store_names, store_responsible := {},{},{},{}
    || store_products, store_bought_products := {},{}
    
    || clients, client_adresses := {},{}
    || client_names, client_date := {},{}
    || clients_product_bought := {}
    || client_form_payment := {}
    
    || product_name := {}
    || product_description, product_color, product_amount := {},{},{}
    || product_enable, product_category, product_image := {},{},{}
    
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
    // CLIENT (cc=client, dd=date, nn=name)
    add_client(cc, dd, nn) =
    PRE
        (cc : USER & cc /: clients & cc /: users) 
        & nn : NAME
        & dd : DATE
    THEN
        clients := clients \/ {cc}
        || users := users \/ {cc}
        || logged := logged \/ {(cc |-> FALSE)}
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
        || client_names := client_names - {(cc |-> client_names(cc))}
        || client_date := client_date - {(cc |-> client_date(cc))}
        || carts := {cc} <<| carts                      
        || client_adresses := client_adresses - {(cc |-> client_adresses(cc))}
        || client_form_payment := client_form_payment - {(cc |-> client_form_payment(cc))}
    END
    ;
    // PRODUCT (ss=storage, pp=product, rr=responsible, nn=name, dd=description, color=color, aa= amount, ee=enable, ii=image, ct=category)
    add_product(ss, pp, rr, dd, cc, aa, ee, ii, nn, ct) =
    PRE
        (pp : PRODUCT & pp /: products)
        & ss : STORE & ss : stores & pp /: ran(store_products(ss))
        & rr : USER & rr : users & store_responsible(ss) = rr & logged(rr) = TRUE
        & dd : DESCRIPTION
        & cc : COLOR
        & aa : INT
        & ee : BOOL
        & ii : IMAGE
        & nn : NAME
        & ct : PROD_CATEGORY
    THEN
        products := products \/ {pp}
        || product_name := product_name \/ {(pp |-> nn)}
        || product_description := product_description \/ {(pp |-> dd)}
        || product_color := product_color \/ {(pp |-> cc)}
        || product_amount := product_amount \/ {(pp |-> aa)}
        || product_enable := product_enable \/ {(pp |-> ee)}
        || product_image := product_image \/ {(pp |-> ii)}
        || product_category := product_category \/ {(pp |-> ct)}
        || store_products(ss) := store_products(ss) <- pp
    END
    ;
    remove_product(ss, pp, rr) =
    PRE
        ss : STORE & ss : stores & pp : ran(store_products(ss))
        & rr : USER & rr : users & store_responsible(ss) = rr & logged(rr) = TRUE
        & (pp : PRODUCT & pp : products)
    THEN
        products := products - {pp}
        || product_name := product_name - {(pp |-> product_name(pp))}
        || product_description := product_description - {(pp |-> product_description(pp))}
        || product_color := product_color - {(pp |-> product_color(pp))}
        || product_amount := product_amount - {(pp |-> product_amount(pp))}
        || product_enable := product_enable - {(pp |-> product_enable(pp))}
        || product_image := product_image - {(pp |-> product_image(pp))}
        || product_category := product_category - {(pp |-> product_category(pp))}
        || store_products := store_products - {(ss |-> store_products(ss))}
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
    ;
    // BUYING (cc=client, fp=form payment, aar=address)
    default_buying_items(cc, fp, add) =
    PRE
        cc : USER & cc : clients & logged(cc) = TRUE 
        & carts(cc) /= {} & card(carts(cc)) > 0
        & fp : FORM_PAYMENT 
        & add : ADRESS
    THEN
        ANY pp, ss  
        WHERE ss: STORE & ss : stores & pp : PRODUCT & pp : products & pp : dom(carts(cc)) & pp : ran(store_products(ss)) THEN
            IF pp : dom(clients_product_bought(cc)) THEN
                clients_product_bought(cc) := clients_product_bought(cc) <+ {(pp |-> clients_product_bought(cc)(pp) + carts(cc)(pp))}
                || store_bought_products(ss) := store_bought_products(ss) <+ {(pp |-> store_bought_products(ss)(pp) + carts(cc)(pp))}
            ELSE
                clients_product_bought(cc) := clients_product_bought(cc) \/ {(pp |-> carts(cc)(pp))}
                || store_bought_products(ss) := store_bought_products(ss) \/ {(pp |-> carts(cc)(pp))}
            END
            || carts(cc) := {}            
            || IF fp /: ran(client_form_payment(cc)) THEN
                client_form_payment(cc) := client_form_payment(cc) <- fp
            END
            || IF add /: ran(client_adresses(cc)) THEN
                client_adresses(cc) := client_adresses(cc) <- add
            END
        END
    END
    ;
    automatic_buying_items(cc) =
    PRE
        cc : USER & cc : clients & logged(cc) = TRUE 
        & carts(cc) /= {} & card(carts(cc)) > 0
        & card(client_form_payment(cc)) > 0
        & card(client_adresses(cc)) > 0
    THEN
        ANY pp, ss  
        WHERE ss: STORE & ss : stores & pp : PRODUCT & pp : products & pp : dom(carts(cc)) & pp : ran(store_products(ss)) THEN
            IF pp : dom(clients_product_bought(cc)) THEN
                clients_product_bought(cc) := clients_product_bought(cc) <+ {(pp |-> clients_product_bought(cc)(pp) + carts(cc)(pp))}
                || store_bought_products(ss) := store_bought_products(ss) <+ {(pp |-> store_bought_products(ss)(pp) + carts(cc)(pp))}
            ELSE
                clients_product_bought(cc) := clients_product_bought(cc) \/ {(pp |-> carts(cc)(pp))}
                || store_bought_products(ss) := store_bought_products(ss) \/ {(pp |-> carts(cc)(pp))}
            END
            || carts(cc) := {}

        END
    END
    ;
    // LISTS
    
    // bought items by client
    v_bought_items_by_client <-- bought_items_by_client(cc) =
    PRE
        cc : USER & cc : clients & cc : users & logged(cc) = TRUE
        & card(clients_product_bought(cc)) > 0
    THEN    
        ANY ii
        WHERE ii : dom(clients_product_bought(cc)) THEN 
            v_bought_items_by_client := product_name(ii)
        END
    END
    ;
    // most bought items by category
    v_most_bought_items_by_category <-- most_bought_items_by_category(ss, cc) =
    PRE
        ss : STORE & ss : stores & cc : PROD_CATEGORY & logged(store_responsible(ss)) = TRUE
    THEN    
        ANY pp
        WHERE pp : PRODUCT & pp : products & pp : ran(store_products(ss)) & product_category(pp) = cc 
            & {pp} = store_bought_products(ss)~[{max(ran(store_bought_products(ss)))}] THEN
            
            v_most_bought_items_by_category :=  product_name(pp)
        END
    END
END