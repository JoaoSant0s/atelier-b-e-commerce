/* projeto_m
 * Author: Ricar
 * Creation date: 06/05/2019
 */
MACHINE
    projeto_m
SEES projeto_m_ctx
    
VARIABLES
    users, admins, clients, 
    products, carts,
    
    stores, store_adresses, store_names, store_responsible
    
INVARIANT
    users <: USER
    & admins <: users
    & clients <: users        
    & products <: PRODUCT
    & carts : clients --> (products +-> NATURAL1)
    
    & stores <: STORE
    & store_adresses : stores --> ADRESS
    & store_names : stores --> NAME
    & store_responsible : stores --> USER
       
INITIALISATION
    users, admins, clients :=  {},{},{}
    || products, carts := {},{}
    || stores, store_adresses, store_names, store_responsible := {},{},{},{}
OPERATIONS
    
    // STORE (ss=store,  rr== responsible, aa=adress, nn=name) 
    add_store(ss, rr, aa, nn) =
    PRE
        (ss : STORE & ss /: stores) 
        & (rr : USER & rr : users)
        & aa : ADRESS
        & nn : NAME
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
    THEN
        stores := stores - {ss}
        || store_adresses := store_adresses - {(ss |-> store_adresses(ss))}
        || store_names := store_names - {(ss |-> store_names(ss))}
        || store_responsible := store_responsible - {(ss |-> store_responsible(ss))}
    END
END