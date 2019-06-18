/* projeto_m
 * Author: Ricar
 * Creation date: 06/05/2019
 */
MACHINE
    projeto_m
SEES projeto_m_ctx

CONCRETE_CONSTANTS
    admin0

PROPERTIES
    admin0 : USER
ABSTRACT_VARIABLES
    users , admins ,
    products , carts ,
    logged ,

    stores , store_addresses , store_names , store_responsible ,
    store_products , store_bought_products ,

    store_managers ,

    clients , client_addresses , client_names , client_date ,
    client_form_payment ,
    clients_product_bought ,

    product_name ,
    product_description , product_color , product_amount , product_enable ,
    product_image , product_category

INVARIANT
    users <: USER
    & admins <: users
    & admins : FIN ( admins )
    & clients <: users
    & store_managers <: users
    & logged : users --> BOOL
    & logged : dom ( logged ) +-> ran ( logged )

    & stores <: STORE
    & products <: PRODUCT
    & products : FIN ( products )
    & carts : clients --> ( products +-> NAT1 )
    & clients_product_bought : clients --> ( products +-> NAT1 )

    // STORE
    & store_addresses : stores --> ADDRESS
    & store_names : stores --> NAME
    & store_responsible : stores --> USER
    & store_products : stores --> seq ( PRODUCT )
    & store_bought_products : stores --> ( products +-> NAT1 )

    //CLIENT
    & client_addresses : clients --> seq ( ADDRESS )
    & client_names : clients --> NAME
    & client_date : clients --> DATE
    & client_form_payment : clients --> seq ( FORM_PAYMENT )

    //PRODUCT
    & product_description : products --> DESCRIPTION
    & product_color : products --> COLOR
    & product_amount : products --> NAT1
    & product_enable : products --> BOOL
    & product_image : products --> IMAGE
    & product_name : products --> NAME
    & product_category : products --> PROD_CATEGORY

INITIALISATION
    users , admins , store_managers , logged := {} , {} , {} , {}
    || products , carts := {} , {}
    || stores , store_addresses , store_names , store_responsible := {} , {} , {} , {}
    || store_products , store_bought_products := {} , {}

    || clients , client_addresses := {} , {}
    || client_names , client_date := {} , {}
    || clients_product_bought := {}
    || client_form_payment := {}

    || product_name := {}
    || product_description , product_color , product_amount := {} , {} , {}
    || product_enable , product_category , product_image := {} , {} , {}
OPERATIONS

    // MAIN ADMIN    
    add_main_admin =
    PRE
        ( admin0 : USER & card ( admins ) = 0 )
        //New conditions
        & logged \/ { admin0 |-> FALSE } : users \/ { admin0 } --> BOOL
        & logged \/ { admin0 |-> FALSE } : dom ( logged \/ { admin0 |-> FALSE } ) +-> ran ( logged \/ { admin0 |-> FALSE } )
    THEN
        users := users \/ { admin0 }
        || admins := admins \/ { admin0 }
        || logged := logged \/ { ( admin0 |-> FALSE ) }
    END
    ;

    // LOGIN
    login ( uu ) =
    PRE
        uu : USER & uu : users
         & ! ff . ( ff : dom ( logged ) => logged ( ff ) = FALSE )
    THEN
        logged ( uu ) := TRUE
    END
    ;
    logout ( uu ) =
    PRE
        uu : USER & uu : users & logged ( uu ) = TRUE
    THEN
        IF uu : clients THEN
            logged ( uu ) := FALSE
            || carts ( uu ) := {}
        ELSE
            logged ( uu ) := FALSE
        END
    END
    ;

    // STORE MANAGERS (ss=store manager, aa = admin)
    add_store_manager ( ss , aa ) =
    PRE
        ( aa : USER & aa : admins & aa : users & logged ( aa ) = TRUE )
        & ss : USER & ss /: store_managers & ss /: users
        //New conditions
        & logged \/ { ss |-> FALSE } : users \/ { ss } --> BOOL
    THEN
        users := users \/ { ss }
        || store_managers := store_managers \/ { ss }
        || logged := logged \/ { ( ss |-> FALSE ) }
    END
    ;
    remove_store_manager ( ss , aa ) =
    PRE
        ( aa : USER & aa : admins & aa : users & logged ( aa ) = TRUE )
        & ss : USER & ss : store_managers & ss : users & ss /: ran ( store_responsible )
        //New conditions
        & admins <: users - { ss }
        & clients <: users - { ss }
    THEN
        store_managers := store_managers - { ss }
        || users := users - { ss }
        || logged := { ss } <<| logged
    END
    ;

    // STORE (ss=store,  rr== responsible, aa=address, nn=name, ad=admin)
    add_store ( ss , rr , aa , nn , ad ) =
    PRE
        ( ss : STORE & ss /: stores )
        & ( rr : USER & rr : store_managers )
        & ss /: dom ( store_responsible )
        & aa : ADDRESS
        & nn : NAME
        & ad : admins
        & logged ( ad ) = TRUE
        //New Conditions
        & store_addresses \/ { ss |-> aa } : stores \/ { ss } --> ADDRESS
        & store_names \/ { ss |-> nn } : stores \/ { ss } --> NAME
        & store_responsible \/ { ss |-> rr } : stores \/ { ss } --> USER
        & store_products \/ { ss |-> {} } : stores \/ { ss } --> seq ( PRODUCT )
    THEN
        stores := stores \/ { ss }
        || store_addresses := store_addresses \/ { ( ss |-> aa ) }
        || store_names := store_names \/ { ( ss |-> nn ) }
        || store_responsible := store_responsible \/ { ( ss |-> rr ) }
        || store_products := store_products \/ { ( ss |-> <> ) }
        || store_bought_products ( ss ) := {}
    END
    ;
    remove_store ( ss ) =
    PRE
        ( ss : STORE & ss : stores )
        & ss : dom ( store_responsible )
        & store_responsible ( ss ) : dom ( logged )
        & logged ( store_responsible ( ss ) ) = TRUE
        // New Conditions
        & ss : dom ( store_addresses )
        & store_addresses - { ss |-> store_addresses ( ss ) } : stores - { ss } --> ADDRESS
        & store_names - { ss |-> store_names ( ss ) } : stores - { ss } --> NAME
        & store_responsible - { ss |-> store_responsible ( ss ) } : stores - { ss } --> USER
        & store_bought_products : stores - { ss } --> ( products +-> NAT1 )
    THEN
        stores := stores - { ss }
        || store_addresses := store_addresses - { ( ss |-> store_addresses ( ss ) ) }
        || store_names := store_names - { ( ss |-> store_names ( ss ) ) }
        || store_responsible := store_responsible - { ( ss |-> store_responsible ( ss ) ) }
        || store_products := store_products - { ( ss |-> store_products ( ss ) ) }
    END
    ;
    // CLIENT (cc=client, dd=date, nn=name, aa = address, fp = form payment)
    add_client ( cc , dd , nn ) =
    PRE
        ( cc : USER & cc /: clients & cc /: users & cc /= admin0 )
        & nn : NAME
        & dd : DATE
        & ! ff . ( ff : dom ( logged ) => logged ( ff ) = FALSE )
        // New Conditions
        & client_names \/ { cc |-> nn } : clients \/ { cc } --> NAME
        & carts \/ { cc |-> {} } : clients \/ { cc } --> ( products +-> NAT1 )
        & client_date \/ { cc |-> dd } : clients \/ { cc } --> DATE
        & logged \/ { cc |-> FALSE } : users \/ { cc } --> BOOL
    THEN
        users := users \/ { cc }
        || clients := clients \/ { cc }
        || logged := logged \/ { ( cc |-> FALSE ) }
        || client_names := client_names \/ { ( cc |-> nn ) }
        || client_date := client_date \/ { ( cc |-> dd ) }
        || carts := carts \/ { ( cc |-> {} ) }
        || client_addresses ( cc ) := <>
        || client_form_payment ( cc ) := <>
        || clients_product_bought ( cc ) := {}
    END
    ;
    remove_client ( cc , aa ) =
    PRE
        ( cc : USER & cc : clients & cc : users )
        & ( aa : USER & aa : admins & aa : users )
        & cc : dom ( logged )
        & ( logged ( cc ) = TRUE )
        //New conditions
        & admins <: users - { cc }
        & store_managers <: users - { cc }
        & clients_product_bought : clients - { cc } --> ( products +-> NAT1 )
    THEN
        clients := clients - { cc }
        || users := users - { cc }
        || logged := { cc } <<| logged
        || client_names := client_names - { ( cc |-> client_names ( cc ) ) }
        || client_date := client_date - { ( cc |-> client_date ( cc ) ) }
        || carts := { cc } <<| carts
        || client_addresses := client_addresses - { ( cc |-> client_addresses ( cc ) ) }
        || client_form_payment := client_form_payment - { ( cc |-> client_form_payment ( cc ) ) }
    END
    ;
    // PRODUCT (pp=product, ss=storage, nn=name, dd=description, color=color, aa= amount, ee=enable, ii=image, ct=category)
    add_product ( pp , ss , dd , cc , aa , ee , ii , nn , ct ) =
    PRE
        pp : PRODUCT
        & ss : STORE & ss : stores
        & store_responsible ( ss ) : dom ( logged )
        & logged ( store_responsible ( ss ) ) = TRUE
        & pp /: ran ( store_products ( ss ) )
        & dd : DESCRIPTION
        & cc : COLOR
        & aa : NAT1
        & ee : BOOL
        & ii : IMAGE
        & nn : NAME
        & ct : PROD_CATEGORY
        //New conditions
        & store_products ( ss ) : seq ( ran ( store_products ( ss ) ) )
        & carts : clients --> ( products \/ { pp } +-> NAT1 )
        & product_description \/ { pp |-> dd } : products \/ { pp } --> DESCRIPTION
        & product_color \/ { pp |-> cc } : products \/ { pp } --> COLOR
        & product_amount \/ { pp |-> aa } : products \/ { pp } --> NAT1
        & product_enable \/ { pp |-> ee } : products \/ { pp } --> BOOL
        & product_image \/ { pp |-> ii } : products \/ { pp } --> IMAGE
        & product_name \/ { pp |-> nn } : products \/ { pp } --> NAME
        & product_category \/ { pp |-> ct } : products \/ { pp } --> PROD_CATEGORY
        & clients_product_bought : clients --> ( products \/ { pp } +-> NAT1 )
        & store_bought_products : stores --> ( products \/ { pp } +-> NAT1 )
    THEN
        products := products \/ { pp }
        || product_description := product_description \/ { ( pp |-> dd ) }
        || product_color := product_color \/ { ( pp |-> cc ) }
        || product_amount := product_amount \/ { ( pp |-> aa ) }
        || product_enable := product_enable \/ { ( pp |-> ee ) }
        || product_image := product_image \/ { ( pp |-> ii ) }
        || product_name := product_name \/ { ( pp |-> nn ) }
        || product_category := product_category \/ { ( pp |-> ct ) }
        || store_products ( ss ) := store_products ( ss ) <- pp
    END
    ;
    remove_product ( ss , pp ) =
    PRE
        pp : products
        & ss : stores
        & store_responsible ( ss ) : dom ( logged )
        & logged ( store_responsible ( ss ) ) = TRUE
        & pp : ran ( store_products ( ss ) )
        //New conditions    
        & carts : clients --> ( products - { pp } +-> NAT1 )
        & clients_product_bought : clients --> ( products - { pp } +-> NAT1 )
        & store_bought_products : stores --> ( products - { pp } +-> NAT1 )
        & product_description - { pp |-> product_description ( pp ) } : products - { pp } --> DESCRIPTION
        & product_color - { pp |-> product_color ( pp ) } : products - { pp } --> COLOR
        & product_amount - { pp |-> product_amount ( pp ) } : products - { pp } --> NAT1
        & product_enable - { pp |-> product_enable ( pp ) } : products - { pp } --> BOOL
        & product_image - { pp |-> product_image ( pp ) } : products - { pp } --> IMAGE
        & product_name - { pp |-> product_name ( pp ) } : products - { pp } --> NAME
        & product_category - { pp |-> product_category ( pp ) } : products - { pp } --> PROD_CATEGORY
        & store_products - { ss |-> store_products ( ss ) } : stores --> seq ( PRODUCT )
    THEN
        products := products - { pp }
        || product_name := product_name - { ( pp |-> product_name ( pp ) ) }
        || product_description := product_description - { ( pp |-> product_description ( pp ) ) }
        || product_color := product_color - { ( pp |-> product_color ( pp ) ) }
        || product_amount := product_amount - { ( pp |-> product_amount ( pp ) ) }
        || product_enable := product_enable - { ( pp |-> product_enable ( pp ) ) }
        || product_image := product_image - { ( pp |-> product_image ( pp ) ) }
        || product_category := product_category - { ( pp |-> product_category ( pp ) ) }
        || store_products := store_products - { ( ss |-> store_products ( ss ) ) }
    END
    ;
    // CARTS ( pp=product, aa=amount, cc=client)
    add_product_to_cart ( pp , aa , cc ) =
    PRE
        pp : PRODUCT & pp : products
        & aa : NAT1
        & cc : USER & cc : clients & logged ( cc ) = TRUE
        & product_amount ( pp ) >= aa
        & product_enable ( pp ) = TRUE
        // New Conditions
        & carts <+ { cc |-> ( carts ( cc ) <+ { pp |-> carts ( cc ) ( pp ) + aa } ) } : clients --> ( products +-> NAT1 )
    THEN
        IF pp : dom ( carts ( cc ) ) THEN
            carts ( cc ) := carts ( cc ) <+ { ( pp |-> carts ( cc ) ( pp ) + aa ) }
        ELSE
            carts ( cc ) := carts ( cc ) \/ { ( pp |-> aa ) }
        END
    END
    ;
    remove_product_of_cart ( pp , aa , cc ) =
    PRE
        pp : PRODUCT & pp : products
        & aa : NAT1
        & cc : USER & cc : clients & logged ( cc ) = TRUE
        & cc : dom ( carts )
        & pp : dom ( carts ( cc ) )
        & carts ( cc ) ( pp ) >= aa
        & product_enable ( pp ) = TRUE
        //New Conditions
        & carts <+ { cc |-> ( carts ( cc ) <+ { pp |-> carts ( cc ) ( pp ) - aa } ) } : clients --> ( products +-> NAT1 )
    THEN
        IF carts ( cc ) ( pp ) = aa THEN
            carts ( cc ) := { pp } <<| carts ( cc )
        ELSE
            carts ( cc ) := carts ( cc ) <+ { ( pp |-> carts ( cc ) ( pp ) - aa ) }
        END


    END
    ;
    // BUYING (cc=client, fp=form payment, aar=address)
    buying_items ( cc , fp , add ) =
    PRE
        cc : clients & logged ( cc ) = TRUE
        & cc : dom ( carts )
        & carts ( cc ) : FIN ( carts ( cc ) )
        & card ( carts ( cc ) ) > 0
        & fp : FORM_PAYMENT
        & add : ADDRESS
        & card ( products ) > 0
        & card ( dom ( carts ( cc ) ) ) > 0
    THEN
        ANY pp , ss
        WHERE ss : stores & pp : products
            & ss : dom ( store_products ) & ss : dom ( store_bought_products )
            & pp : dom ( carts ( cc ) ) & pp : ran ( store_products ( ss ) ) THEN
            carts ( cc ) := {}
            || IF pp : dom ( clients_product_bought ( cc ) ) THEN
                clients_product_bought ( cc ) := clients_product_bought ( cc ) <+ { ( pp |-> clients_product_bought ( cc ) ( pp ) + carts ( cc ) ( pp ) ) }
                || store_bought_products ( ss ) := store_bought_products ( ss ) <+ { ( pp |-> store_bought_products ( ss ) ( pp ) + carts ( cc ) ( pp ) ) }
                ELSE
                    clients_product_bought ( cc ) := clients_product_bought ( cc ) \/ { ( pp |-> carts ( cc ) ( pp ) ) }
                    || store_bought_products ( ss ) := store_bought_products ( ss ) \/ { ( pp |-> carts ( cc ) ( pp ) ) }
                END
            || IF fp /: ran ( client_form_payment ( cc ) ) THEN
                    client_form_payment ( cc ) := client_form_payment ( cc ) <- fp
                END
            || IF add /: ran ( client_addresses ( cc ) ) THEN
                    client_addresses ( cc ) := client_addresses ( cc ) <- add
                END
        END
    END
    ;
    // LISTS

    // bought items by client
    v_bought_items_by_client <-- bought_items_by_client ( cc ) =
    PRE
        cc : USER & cc : clients & cc : users & logged ( cc ) = TRUE
        & clients_product_bought ( cc ) : FIN ( clients_product_bought ( cc ) )
        & cc : dom ( clients_product_bought )
        & card ( clients_product_bought ( cc ) ) > 0
        & card ( products ) > 0
    THEN
        v_bought_items_by_client := clients_product_bought ( cc )
    END
END
