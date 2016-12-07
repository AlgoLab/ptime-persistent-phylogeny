/*
  Copyright Gabriella Trucco 2015-2016
*/

// TODO: check global var specieRealizzate
// go to the next solution, if it is not solution for the first graph

#include<stdlib.h>
#include<stdio.h>
#include <iostream>
#include <fstream>
#include <time.h>

using namespace std;

int** GRB;
int* soluzione; // character sequence
int* setSpecie;
int ** estesa;
int* specieRealizzate;
int righeO, colonneO;
int indice_path; // path array index, to insert a new node
int* percorso; // path from source to sink. Check if it is feasible
int* sorgenti;
int* end_nodes;
int* sorgenti_potenziali; //usato per aggiornare diagramma Hasse nella ricerca di una specie ammissibile
int* sink;
int* in_deg;
int ** matrice;   //matrice di partenza, con colonne ordinate per numero decrescente di 1
int ** matriceO;
int** inclusioni;
int** hasse;
int numero_conflitti;
int gc_vuoto; //1: empty; 0: the graph has some conflict
int** archi_gabry;
int* comp_colonne; //componenti matrice di partenza
int* comp_righe;   //componenti matrice di partenza
char* mapping_chars;
FILE* file;
ofstream outsi;
ofstream outno;
int componenti_matrice;
int* massimali;
int** matrice_indotta;
int righe_indotta;
int colonne_indotta;
int** matrice_cc;
int righe_cc;
int colonne_cc;
int* specie_realizzate;
int* car_universali;
int* car_attivi;
int** matriceMC; //matrice di massimali compattata
int righeMC;
int colonneMC;
int* corrispondenza_cc; //tabella di corripondenza tra colonne di matrici indotte
int* corrispondenzaMC;

#define         NOTVISITED              0
#define         VISITED                 1


class ConflictGraph {
public:

        ConflictGraph (int** m, int righe, int colonne);

        bool is_a_graph_with_only_singletons ();
        bool is_a_simple_graph ();
        bool is_connected();
        bool is_a_singleton (int car);
        int* compute_connected_component (int i);
        int print_connected_component (int* cc);
        int size_connected_component (int* cc);

        bool red_conflict (int** m, int righe, int colonne, int i, int j);      // method that checks if character i and character j are in red conflict
        bool specie_non_realizzata(int**m, int colonne, int k);
        bool carattere_connesso(int** m, int righe, int k);
        // Value extraction methods - inlined - they allow the value of _vertex to be private
        int get_vertex () const { return _vertex; };
        int get_species () const { return _species; };

        int insert_edge (int i, int j);

        int compute_components();
        int scorri_colonna(int colonna); //per calcolare le componenti del grafo

        int print_graph ();
        int reset_status ();


        int** cgraph;                   // another representation of the conflict graph in which the arcs are indexed
        int edges;                              // number of edges in the graph

        int* species_sequence;          // S_q, i.e., le specie in S* ordinate a seconda del numero di 1


private:

        struct node {
                int value; node* next;
                node(int x, node* t) {value = x; next = t; }
        };

        typedef node* link;
        link* adj;              // the array containing the adjunct lists
        int _vertex;    // number of vertexes in the graph, it corresponds to the number of characters
        int _species;
        int* mapping;
        int* status;                    // an array that records the status of the visits to ???? nodes or verteces???che contiene lo status delle visite dei vari nodi
};

// Constructor
// Construct the conflict graph from matrix m, which could have some rows removed
ConflictGraph::ConflictGraph (int** m, int righe, int colonne) {
        int i, j,x;
        link t;
        _vertex = colonne;
        _species = righe;

        cgraph = new int* [get_vertex()];
        for (i = 0; i < get_vertex(); i++){
                cgraph[i] = new int[get_vertex()];
        }
        // initialize the graph with no arcs => all 0s
        for (i = 0; i < get_vertex(); i++) {
                for (j = 0; j < get_vertex(); j++) {
                        cgraph[i][j] = 0;
                }
        }
        edges = 0;                      // initially there are no edges in the graph

        // create the array containing the adjunct lists representing the conflict graph
        // the lists are initially empty
        adj = new link [get_vertex()];
        for (i = 0; i < get_vertex(); i++) {
                adj[i] = NULL;
        }


        for (i = 0; i < get_vertex(); i++) {
                if(carattere_connesso(m, righe, i)){
                        for (j = i + 1; j < get_vertex(); j++) {
                                if(carattere_connesso(m, righe, j)){
                                        if (red_conflict(m, righe, colonne, i, j) == true) {
                                                insert_edge(i, j);                                              // add the arc in the adjunct list
                                                cgraph[i][j] = cgraph[j][i] = ++edges;  // add the arc in the adjunct matrix
                                        }
                                }
                        }
                }
        }

        numero_conflitti=edges;
        if (numero_conflitti>0) gc_vuoto=0;
        else gc_vuoto=1;

        // set all the vertexes as NOTVISITED
        // serve per poi usare la funzione di visita/lettura del grafo
        status = new int [_vertex];
        for (i = 0; i < _vertex; i++) {
                status[i] = NOTVISITED;
        }

        mapping = new int [get_vertex()];
        for (i = 0; i < get_vertex(); i++) {
                mapping[i] = i;
        }

        archi_gabry=new int*[edges];
        for(i=0; i<edges; i++) archi_gabry[i]=new int[2];

        for(i=0; i<edges;i++){
                for(j=0; j<2; j++)
                        archi_gabry[i][j]=-1;
        }
        x=0;

        for (i = 0; i < get_vertex(); i++) {
                t = adj[i];
                while (t != NULL) {
                        if (i < t->value) {
                                archi_gabry[x][0]= i;
                                archi_gabry[x][1]=t->value;
                                x++;
                        }
                        t = t->next;
                }
        }
}

// A method to insert a new arc in the graph between the vertex of character i and the vertex of character j
int ConflictGraph::insert_edge(int i, int j) {

        if (i < 0 || i > get_vertex()) {
                cout << "ConflictGraph::insert_edge(): Index of character out of range!" << endl;
                exit(-1);
        }

        if (j < 0 || j > get_vertex()) {
                cout << "ConflictGraph::insert_edge(): Index of character out of range!" << endl;
                exit(-1);
        }

        // since the graph is undirected, it adds a node in the adjunct list of both i and j
        adj[i] = new node(j, adj[i]);
        adj[j] = new node(i, adj[j]);

        return 0;
};

// method that checks if character i and character j are in red conflict
// NB: i and j are the indexes of the matrix
bool ConflictGraph::red_conflict(int** m, int righe, int colonne, int i, int j) {
        int k;
        int flag1 = 0;
        int flag2 = 0;
        int flag3 = 0;
        int flag4 = 0;

// controllo che i due caratteri appartengono alla stessa componente e che le specie considerate non siano ancora state realizzate
        if (comp_colonne[i]==comp_colonne[j]){
                for (k = 0; k < righe; k++) {
                        if(specie_non_realizzata(m,colonne,k)){

                                if ((matrice[k][i] == 0 ) && (matrice[k][j] == 0) && (comp_righe[k]==comp_colonne[i])) flag1 = 1;
                                if ((matrice[k][i] == 0) && (matrice[k][j] == 1) && (comp_righe[k]==comp_colonne[i])) flag2 = 1;
                                if (((matrice[k][i] == 1)) && (matrice[k][j] == 0) && (comp_righe[k]==comp_colonne[i])) flag3 = 1;
                                if ((matrice[k][i] == 1) && (matrice[k][j] == 1) && (comp_righe[k]==comp_colonne[i])) flag4 = 1;
                        }
                }
        }
        if (flag1 && flag2 && flag3 && flag4) return true; //sigma nero
        return false;
};

bool ConflictGraph::specie_non_realizzata(int** m, int colonne, int k){
        int i;
        for(i=0; i<colonne; i++){
                if(m[k][i]!=0) return true;
        }
        return false;
}

//il carattere k non è singoletto
bool ConflictGraph::carattere_connesso(int** m, int righe, int k){
        int i;
        for(i=0; i<righe; i++){
                if(m[i][k]!=0) return true;
        }
        return false;
}

int ConflictGraph::print_graph() {
        link t;

        // print the first representation of the graph
        // the arcs and the singletons
        for (int i = 0; i < get_vertex(); i++) {
                t = adj[i];
                while (t != NULL) {
                        if (i < t->value) cout << mapping_chars[i] << " - " << mapping_chars[t->value] << endl;
                        t = t->next;
                }
        }
        return 0;
};

bool ConflictGraph::is_a_simple_graph () {
        int* cc;
        int i, size;
        int singleton_counter = 0;

        // it counts how many singletons are in the graph
        for (i = 0; i < get_vertex(); i++) {
                if (adj[i] == NULL) singleton_counter++;
        }

        // it searches for a non-trivial connected component (with size > 1)
        // if it finds such a component it exits the loop
        for (i = 0; i < get_vertex(); i++) {
                cc = compute_connected_component(i);
                size = size_connected_component(cc);
                //cout << "Dimensione della componente non banale: " << size << endl;
                if (size > 1) break;
        }

        if (size > 1) {
                if (size == (get_vertex() - singleton_counter)) {       // there is only one non-trivial component
                        return true;
                } else {                                                                                        // there is more than one non-trivial component
                        return false;
                }
        } else {                                                                                                // there are only singletons
                return false;
        }
}

bool ConflictGraph::is_connected () {
        int* cc;
        int i, size;

        // it searches for a non-trivial connected component (with size > 1)
        // if it finds such a component it exits the loop
        for (i = 0; i < get_vertex(); i++) {
                cc = compute_connected_component(i);
                size = size_connected_component(cc);
                if (size > 1) break;
        }

        if (size > 1) {
                if (size == (get_vertex())) {   // there is only one non-trivial component
                        return true;
                } else {                                                                                        // there is more than one non-trivial component
                        return false;
                }
        } else {                                                                                                // there are only singletons
                return false;
        }
}

bool ConflictGraph::is_a_graph_with_only_singletons () {
        int singleton_counter = 0;
        int i;
        for (i = 0; i < get_vertex(); i++) {
                if (adj[i] == NULL) singleton_counter++;
        }
        if (singleton_counter == get_vertex()) return true;             // if all the vertexes are singletons (not connected), return true

        return false;
}

bool ConflictGraph::is_a_singleton (int car) {
        if (adj[car] == NULL) return true;
        return false;
}

int ConflictGraph::size_connected_component(int* cc) {
        int counter = 0;

        for (int i = 0; (i < get_vertex() && cc[i] != -1); i++) {
                counter++;
        }

        return counter;
};

int* ConflictGraph::compute_connected_component(int i) {
        int stack[get_vertex()+1]; // da verificare se e' giusto il + 1 che ho aggiunto
        int top = 1;
        //int index_character;
        link t;
        int* connected_vertex = new int [get_vertex()]; // DA VERIFICARE SE LA DIMENSIONE DEVE ESSERE AUMENTATA DI UNO
        // NELLA PEGGIORE DELLE IPOTESI HO CHE TUTTI I CARATTERI APPARTENGONO ALLA CC
        // E ALLORA NON HO PIU' SPAZIO PER METTERCI IL -1
        int j = 0;

        if (i < 0 || i >= get_vertex()) {
                cout << "GraphRB::compute_connected_component(): Index out of range!" << endl;
                exit(-1);
        }
        //index_character = get_species() + i; // compute the index of the character in terms of the array adj

        stack[0] = -1;  // set the exit condition

        reset_status();

        stack[top] = i;
        status[i] = VISITED;

        while (1) {
                // exit condition
                if (stack[top] == -1)  {
                        break;
                }

                connected_vertex[j] = stack[top];
                j++;

                t = adj[stack[top]];
                top--;

                // put in the stack all adjunct vertexes that has not been visited yet
                while (t != NULL) {
                        if (status[t->value] == NOTVISITED ) {
                                top++;
                                stack[top] = t->value;
                                status[t->value] = VISITED;
                        } // end IF

                        t = t->next;
                }
        }

        connected_vertex[j] = -1;       // set the end of the connected species component
        return connected_vertex;
};

int ConflictGraph::reset_status() {
        int i;
        for (i = 0; i < _vertex; i++) {
                status[i] = NOTVISITED;
        }

        return 0;
};

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
void readMatrix(int** matrice, int righe, int colonne);
void printMatrix(int ** a, int m, int n);
int calcola_componenti(int** matrice, int righe, int colonne);
int componenti_colonna(int car, int** matrice, int ri, int co);
int componenti_riga(int r, int c_iniziale, int** matrice, int ri, int co);
void calcola_massimali(int colonne, int* caratteri_universali, int** matrice, int righe, int* specie_realizzate);
int incluso(int c, int* caratteri_universali, int righe, int* specie_realizzate, int** matrice, int colonne);
int ultimo_carattere(int c, int colonne, int* caratteri_universali);
int no_massimali(int* massimali, int colonne);
void indotta_cc(int componente);
void indotta_massimali(int**matrice, int righe, int colonne, int* massimali);
int sIncluded(int** matrice, int colonne, int s1, int s2);
int conta_uni(int** m, int riga, int colonne);
int trova_sorgenti(int colonna, int righe);
int trova_sink(int riga, int righe);
int inDeg(int colonna, int righe);
int outDeg(int riga, int righe);
void percorso_semplice(int righe);
void aggiungi_nodo(int s, int righe);
void trova_successivo(int nodo, int righe);
int cerca_ammissibile(int righe);
void realizza_specie(int** matrice, int righe, int colonne, int specie, int* specie_realizzate, int* caratteri_universali, int* caratteri_attivi, int** Grb, int* soluzione_massimali);
void realizza_specie(int** Grb, int righe, int colonne, int specie, int* specie_realizzate, int* caratteri_universali, int* caratteri_attivi);
void rendi_universale(int** matrice, int righe, int colonne, int i,int** Grb,  int* caratteri_universali, int* caratteri_attivi, int* specie_realizzate, int* soluzione_massimali);  //i: carattere da rendere universale
void rendi_universale(int** Grb, int righe, int colonne, int i, int* caratteri_universali, int* caratteri_attivi, int* specie_realizzate);  //i: carattere da rendere universale
int valuta_colonna(int** Grb, int righe, int colonne, int carattere, int* tspecie, int* tcarattere);
int valuta_riga(int** Grb, int righe, int colonne, int specie, int* tspecie, int* tcarattere);
void aggiorna_caratteri_attivi(int** Grb, int righe, int colonne, int* caratteri_attivi, int* specie_realizzate);
void aggiorna_specie_realizzate(int** Grb, int righe, int colonne, int* specie_realizzate);
int valuta_colonna(int** matrice, int righe, int colonne, int carattere, int** Grb, int* tspecie, int* tcarattere);
int valuta_riga(int** matrice, int righe, int colonne, int specie, int** Grb, int* tspecie, int* tcarattere);
void aggiorna_caratteri_attivi(int** matrice, int righe, int colonne, int* caratteri_attivi, int** Grb, int* specie_realizzate);
void aggiorna_specie_realizzate(int** matrice, int righe, int colonne, int* specie_realizzate, int** Grb);
//void aggiorna_gc(int** matrice, int righe, int colonne);
bool specie_realizzata(int** matrice,int righe,int colonne,int specie, int* caratteri_universali);
void aggiorna_sorgenti_potenziali(int specie);
int included(int** matrice, int righe, int colonne, int s1, int s2);
void percorso_cicli(int righe);
int verificaEndNode(int n);
void aggiorna_Hasse(int specie);
int determinaEndNode(int cSink);
int inserisciNodo(int nodoCorrente, int nodoDestinazione);
void percorsiSinkEN();
void percorsiENSorgenti();
void copiaSinkEn(int si, int en);
void copiaEnSorgente(int en, int so);
int realizza_percorso();
void estendi(int carattere, int** Grb);
int* riordina_percorso(int* percorso, int righe);
void zigzagPath(int righe);
void percorriZigzag();
void alberoMassimali();
void calcolaSoluzione(int** matrice, int righe, int colonne);
void completaSoluzione(int s);
void trovaMinimali();
int inserito(int c);
int conflitto(int c);
void compattaIndottaMassimali();
int specieDiversa(int s);
int specieUguali(int s1, int s2);
void calcolaZ();
int appartiene(int carattere, int specie);
void aggiornaSoluzione(int minimale);
void trovaSorgenti(int** matrice, int** hasse, int righe, int colonne);
int* costruiscoPercorso(int** matrice, int** hasse, int righe, int colonne, int i, int j);
int trovaSuccessivo(int** matrice, int** hasse, int righe, int colonne, int nodo, int sink);
void riduciMatrice(int** matrice, int righe, int colonne);
void trovaPercorsi(int** matrice, int** hasse, int righe, int colonne);
int determinaIndice(int* soluzione);
void copiaSoluzione(int* soluzione,int indice,int specie, int** matrice, int colonne);
void aggiornaGRB(int** GRB,int righeO,int colonneO,int k,int* specie_realizzate,int* car_universali, int* car_attivi);
int inclusioneCaratteri(int c1, int c2, int** matrice, int righe);
bool colonnaSingoletto(int** matrice,int righe,int colonna);
bool rigaSingoletto(int** matrice,int colonne,int riga);
bool soloSingoletti(int* componenti, int colonne);
int sottomatriceProibita(int ** a, int c1, int c2);
/////////////////////////////////////////////////////////////////////////////////////////////////////////////


int main(int argc, char *argv[]) {
        int i,j,ii,jj;
        char a = 'a';
        char* fileName;

        mapping_chars = new char [29];
        for (i = 0; i < 29; i++) {
                mapping_chars[i] = a;
                a++;
        }

        // check command line (main) arguments
        if (argc != 2) {
                printf("Usage: check infile\n");
                return 0;
        } else {
                fileName = argv[1];
                // open file and check if empty
                if ((file = fopen(fileName, "r")) == NULL) {
                        printf("File %s could not be opened.\n", fileName);
                        return 0;
                }
                if (feof(file)) {
                        printf("File %s is empty.", fileName);
                        return 0;
                }
        }

        fscanf(file, "%d %d", &righeO, &colonneO);

        while(!feof(file)){
                matriceO = (int **)calloc(righeO, sizeof(int *));
                for (i = 0; i < righeO; i++){
                        matriceO[i] = (int *)calloc(colonneO, sizeof(int));
                }
                readMatrix(matriceO,righeO,colonneO);
                printf("\nMatrice nera:---------------------------------------------\n");
                printMatrix(matriceO,righeO,colonneO);


                soluzione=new int[colonneO];
                for(i=0; i<colonneO; i++) soluzione[i]=-1;
                GRB = (int **)calloc(righeO, sizeof(int *));
                for (i = 0; i < righeO; i++){
                        GRB[i] = (int *)calloc(colonneO, sizeof(int));
                }
                for (i = 0; i < righeO; i++){
                        for (j = 0; j < colonneO; j++)
                                GRB[i][j]=matriceO[i][j];
                };

                car_universali=new int[colonneO];
                for(i=0; i<colonneO; i++) car_universali[i]=0;
                car_attivi=new int[colonneO];
                for(i=0; i<colonneO; i++) car_attivi[i]=0;
                specie_realizzate=new int[righeO];
                for(i=0; i<righeO; i++) specie_realizzate[i]=0;

                estesa = (int **)calloc(righeO, sizeof(int *));
                for (i = 0; i < righeO; i++) {
                        estesa[i] = (int *)calloc(2*colonneO, sizeof(int));
                }
                for (i = 0; i < righeO; i++) {
                        for (j = 0; j < 2*colonneO; j++) {
                                estesa[i][j]=-1;
                        }
                }

                //calcolo le componenti e richiamo algo di riduzione su ogni componente
                riduciMatrice(GRB,righeO,colonneO);

                cout<<"SOLUZIONE: ";
                for(ii=0; ii<colonneO; ii++) cout<<soluzione[ii];
                cout<<endl;
                printMatrix(estesa, righeO, colonneO*2);
                //verifica finale sulla matrice estesa
                for (ii = 0; ii < 2*colonneO-1; ii++) {
                        for (jj = ii+1; jj < 2*colonneO; jj++) {
                                if (sottomatriceProibita(estesa,ii,jj) == 1) { //esiste sottomatrice proibita
                                        cout<<"sottomatrice proibita tra colonne "<<ii <<" e "<< jj<<endl;
                                        cout<<"La matrice non ammette soluzione"<<endl;
                                        cout<<"***No Persistent Phylogeny"<<endl;
                                        exit(EXIT_SUCCESS);
                                }
                        }
                }
                cout<<"***Ok Persistent Phylogeny"<<endl;
                exit(EXIT_SUCCESS);

        }

        return 0;
}

//data una matrice di una sola componente connessa, calcola tutti i possibili percorsi safe da radice a sink
void calcolaSoluzione(int**matrice, int righe, int colonne){
        int i,j,k;
        int n_uni;
        inclusioni = new int* [righe];
        for (i = 0; i < righe; i++){
                inclusioni[i] = new int[righe];
        }
        // initialize the graph with no arcs => all 0s
        for (i = 0; i < righe; i++) {
                for (j = 0; j < righe; j++) {
                        inclusioni[i][j] = 0;
                }
        }

        hasse = new int* [righe];
        for (i = 0; i < righe; i++){
                hasse[i] = new int[righe];
        }
        // initialize the graph with no arcs => all 0s
        for (i = 0; i < righe; i++) {
                for (j = 0; j < righe; j++) {
                        hasse[i][j] = 0;
                }
        }

        //1a  calcolo diagramma di Hasse. date n specie, costruisco matrice inclusioni nxn dove cella = 1 se esiste arco che collega specie-riga e specie-colonna
        //è la matrice delle inclusioni, in cui non esiste proprietà transitiva (eliminata al passo successivo)
        for(i=0; i<righe; i++){
                for(j=0; j<righe; j++){
                        if(i!=j){
                                inclusioni[i][j]=sIncluded(matrice, colonne, i, j);
                        }
                }
        }

        for (i = 0; i < righe; i++) {
                for (j = 0; j < righe; j++) {
                        hasse[i][j] = inclusioni[i][j];
                }
        }

        //1b  transitività: date s1 s2 s3, se s1<s2<s3 devo avere archi s1-s2 ed s2-s3 ma non s1-s3
        //per fare questo, devo tenere conto del numero di 1 delle specie. Tengo archi tra specie di livelli consecutivi
        //per ogni riga di inclusioni, se esiste più di un 1, controllo che le due specie che includono non abbiano inclusione tra loro
        // se disgiunte, tengo entrambi gli 1
        // se inclusione, tengo quella con minor numero di 1 e metto a 0 l'altra
        for(i=0; i<righe; i++){
                n_uni=conta_uni(inclusioni, i, righe);
                if(n_uni<2){
                        for(j=0; j<righe; j++) hasse[i][j]=inclusioni[i][j];
                }
                else
                        for(j=0; j<righe-1; j++)
                                if(inclusioni[i][j]==1)
                                        for(k=j+1; k<righe; k++)
                                                if(inclusioni[i][k]==1)
                                                        if((inclusioni[j][k]==1)|(inclusioni[k][j]==1))
                                                                if (inclusioni[j][k]==1)
                                                                        hasse[i][k]=0;
                                                                else
                                                                        hasse[i][j]=0;
        }

        trovaPercorsi(matrice, hasse, righe, colonne);
}


void readMatrix(int** matrice, int righe, int colonne) {
        int i,j;

        for (i = 0; i < righe; i++) {
                for (j = 0; j < colonne; j++) {
                        fscanf(file, "%d", &(matrice[i][j]));
                }
        }

}

// print a matrix to the standard output
void printMatrix(int ** a, int m, int n) {
        int i, j;
        for (i = 0; i < m; i++) {
                for (j = 0; j < n; j++)
                        printf("%d ", a[i][j]);
                cout << endl;
        }
        cout << endl;
}

/**
   computes the connected components of the red-black graph associated to the input matrix.
   comp_colonne and comp_righe store the ID of the component to which a species/character belongs.

   Retuq
*/
int calcola_componenti(int** matrice, int righe, int colonne){
        int i,j, start;
        cout<<"calcola componenti--------------------"<<endl;
        for(i=0; i<righe; i++){
                for(j=0; j<colonne; j++){
                        cout<<matrice[i][j];
                }
                cout<<endl;
        }

        comp_colonne = new int [colonne];
        for(i=0; i<colonne; i++)
                comp_colonne[i]=-1;
        comp_righe = new int [righe];
        for(i=0; i<righe; i++)
                comp_righe[i]=-1;

        bool checked[righe+colonne+1];
        bool reached[righe+colonne+1];
        for(i=0; i<righe+colonne; i++) {
                checked[i] = false;
                reached[i] = false;
        }
        checked[righe+colonne] = true; // sentinel
        reached[righe+colonne] = true; // sentinel
        int num_connected_components = 1;
        for(int component_id=0; ; component_id++, num_connected_components++) {
                /* find the first vertex of the new connected component */
                int current = 0;
                for (; checked[current]; current++) {}
                reached[current] = true;

                do {
                        checked[current] = true;

                        if (current < righe) {
                                for(j=0; j<colonne; j++)
                                        if (matrice[current][j] > 0)
                                                reached[righe+j] = true;
                        } else {
                                for(i=0; i<righe; i++)
                                        if (matrice[i][current-righe] > 0)
                                                reached[i] = true;
                        }

                        for (current=0; current < righe+colonne; current++)
                                if (reached[current] && !checked[current])
                                        break;
                        // for(i=0; i<current; i++) cout<< " ";
                        // cout << "*" << endl;
                } while (current < righe+colonne);

                int source_new_component = righe+colonne;
                for (current=0; current < righe; current++) {
                        if (checked[current] && comp_righe[current] < 0)
                                comp_righe[current] = component_id;
                        if (!checked[current])
                                source_new_component = current;
                }
                for (current=0; current < colonne; current++) {
                        if (checked[righe+current] && comp_colonne[current] < 0)
                                comp_colonne[current] = component_id;
                        if (!checked[current])
                                source_new_component = current;
                }
                // cout << "Final  Reached and checked" << endl;
                // cout << "current=" << current << "->" << source_new_component << endl;
                // for(i=0; i<righe + colonne; i++) cout<< reached[i];
                // cout<<endl;
                // for(i=0; i<righe + colonne; i++) cout<< checked[i];
                // cout<<endl;
                current = source_new_component;
                if (current >= righe + colonne)
                        break;
        }

        for(i=0; i<colonne; i++)
                if(colonnaSingoletto(matrice, righe, i))
                        comp_colonne[i]=-2;  // singleton

        for(i=0; i<righe; i++)
                if(rigaSingoletto(matrice, colonne, i))
                        comp_righe[i]=-2;  // singleton

        cout << "COMP colonne" << endl;
        int num_nontrivial_connected_components = num_connected_components;
        for(i=0; i<colonne; i++) {
                cout<<comp_colonne[i]<<" ";
                if (comp_colonne[i] == -2)
                        num_nontrivial_connected_components--;
        }
        cout<<endl;
        cout << "COMP righe" << endl;
        for(i=0; i<righe; i++)  {
                cout<<comp_righe[i]<<" ";
                if (comp_righe[i] == -2)
                        num_nontrivial_connected_components--;
        }
        cout<<endl;
        cout << num_nontrivial_connected_components << endl;

/* If there are only singletons, return -2 */
        return (num_nontrivial_connected_components == 0) ? -2 : num_nontrivial_connected_components - 1;
}

bool soloSingoletti(int* componenti, int colonne){
        int i;
        for(i=0; i<colonne; i++){
                if(componenti[i]!=-2) return false;
        }
        return true;
}

bool colonnaSingoletto(int** matrice,int righe,int colonna){
        int i;
        for(i=0; i<righe; i++)  {
                if (matrice[i][colonna]!=0) return 0;
        }
        return 1;
}

bool rigaSingoletto(int** matrice,int colonne,int riga){
        int i;
        for(i=0; i<colonne; i++)  {
                if (matrice[riga][i]!=0) return 0;
        }
        return 1;
}

//dato un carattere, controlla dove è a 1 nella colonna e richiama la fx che scorre la riga corrispondente
int componenti_colonna(int car, int** matrice, int ri, int co){
        int i;
        for (i=0;i<ri; i++){
                if (matrice[i][car]==1) {
                        comp_righe[i]=comp_colonne[car];
                        matrice[i][car]=3; //altrimenti va in loop. alla fine riscrivo gli 1
                        componenti_riga(i,car, matrice, ri, co);
                }
                else if (matrice[i][car]==2) {
                        comp_righe[i]=comp_colonne[car];
                        matrice[i][car]=4; //altrimenti va in loop. alla fine riscrivo gli 1
                        componenti_riga(i,car, matrice, ri, co);
                }
        }
        return 0;
}

int componenti_riga(int r, int c_iniziale, int** matrice, int ri, int co){
        int i;
        for (i=0;i<co; i++){
                if (matrice[r][i]==1){
                        matrice[r][i]=3; //altrimenti va in loop. alla fine riscrivo gli 1
                        comp_colonne[i]=comp_colonne[c_iniziale];
                        componenti_colonna(i, matrice, ri, co);  //ricorsione??
                }
                if (matrice[r][i]==2){
                        matrice[r][i]=4; //altrimenti va in loop. alla fine riscrivo gli 1
                        comp_colonne[i]=comp_colonne[c_iniziale];
                        componenti_colonna(i, matrice, ri, co);
                }
        }
        return 0;
}

void calcola_massimali(int colonne, int* caratteri_universali, int** matrice, int righe, int* specie_realizzate){
        int i, cont;

        massimali = (int *) calloc(colonne, sizeof(int));
        for (i = 0; i < colonne; i++)
                massimali[i] = 0;

        for(i=0; i<colonne; i++){
                if(caratteri_universali[i]==0){ //il carattere deve ancora essere realizzato
                        //il carattere non deve essere incluso in uno degli altri caratteri non ancora resi universali
                        //oppure deve essere l'ultimo da rendere universale
                        if((!(incluso(i, caratteri_universali, righe, specie_realizzate, matrice, colonne))) || (ultimo_carattere(i, colonne, caratteri_universali))){
                                // cout<<i<<" massimale"<<endl;
                                massimali[i]=1;
                        }
                }
        }
        if(no_massimali(massimali, colonne)){ //non ho trovato massimali con il blocco precedente ma ci sono ancora caratteri da realizzare
                // i rimanenti caratteri sono tutti massimali - dovrebbero essere uguali tra loro
                for(i=0; i<colonne; i++){
                        if(caratteri_universali[i]==0) massimali[i]=1;
                }
        }
}

//stabilisco se il carattere c è incluso in un altro carattere
int incluso(int c, int* caratteri_universali, int righe, int* specie_realizzate, int** matrice, int colonne){
        int i;
        int incluso; //se 0: non incluso; se >0, incluso

        incluso=0; //ipotizzo inizialmente non sia incluso
        for(i=0; i<colonne; i++){
                if((i!=c)){
                        if(caratteri_universali[i]==0){
                                incluso=incluso + inclusioneCaratteri(c,i, matrice, righe);
                        }
                }
        }
        if (incluso==0) return 0;
        else return 1;
}

//verifico se carattere c1 incluso in carattere c2
int inclusioneCaratteri(int c1, int c2, int** matrice, int righe){
        int i;

        for(i=0; i<righe; i++){
                if((matrice[i][c1]==1) && (matrice[i][c2]==0)) {
                        return 0;
                }
        }
        return 1;

}


int ultimo_carattere(int c, int colonne, int* caratteri_universali){
        int i;

        for(i=0; i<colonne; i++){
                if(i!=c){
                        if (caratteri_universali[i]==0)
                                return 0;
                }
        }
        return 1;
}

int no_massimali(int* massimali, int colonne){
        int i;
        for(i=0; i<colonne; i++){
                if(massimali[i]==1) return 0; //ho trovato un massimale
        }
        return 1;
}

void indotta_cc(int componente){
        int* caratteri;
        int* specie;
        int i,j;
        int i_cc, j_cc;

        righe_cc=0;
        colonne_cc=0;

        caratteri = (int *) calloc(colonneO, sizeof(int));
        for (i = 0; i < colonneO; i++) caratteri[i] = 0;

        specie = (int *) calloc(righeO, sizeof(int));
        for (i = 0; i < righeO; i++) specie[i] = 0;

        //caratteri della componente
        for(i=0; i<colonneO; i++){
                if(comp_colonne[i]==componente) caratteri[i]=1;
        }

        //specie della componente
        for(i=0; i<righeO; i++){
                if(comp_righe[i]==componente) specie[i]=1;
        }

        //numero righe indotta
        for(i=0; i<righeO; i++){
                if(specie[i]==1) righe_cc++;
        }
        //numero colonne indotta
        for(i=0; i<colonneO; i++){
                if(caratteri[i]==1) colonne_cc++;
        }

        corrispondenza_cc=new int [colonne_cc];
        //riempio matrice indotta
        matrice_cc=new int*[righe_cc];
        for(i=0; i<righe_cc; i++){
                matrice_cc[i]=new int [colonne_cc];
        }
        i_cc=0;
        j_cc=0;
        for(i=0;i<righeO; i++){
                if(specie[i]==1){
                        for(j=0; j<colonneO; j++){
                                if(caratteri[j]==1){
                                        matrice_cc[i_cc][j_cc]=GRB[i][j];
                                        corrispondenza_cc[j_cc]=j; //associo alla colonna indotta l'indice della colonna originale per tenere traccia dell'etichetta
                                        //aggiorno indici matrice indotta
                                        if(j_cc!=colonne_cc) j_cc++;
                                        if((j_cc==colonne_cc)&&(i_cc<righe_cc)){
                                                i_cc++;
                                                j_cc=0;
                                        }
                                }
                        }
                }
        }
}

void indotta_massimali(int**matrice, int righe, int colonne, int* massimali){
        int i,j;
        int i_indotta, j_indotta;

        righe_indotta=0;
        colonne_indotta=0;

        int caratteri[colonne];
        for (i = 0; i < colonne; i++) caratteri[i] = 0;

        int specie[righe];
        for (i = 0; i < righe; i++) specie[i] = 0;

//caratteri della matrice indotta
        for(i=0; i<colonne; i++){
                if(massimali[i]==1) caratteri[i]=1;
        }
//specie della matrice indotta
        for(i=0; i<colonne; i++){
                if(caratteri[i]==1){
                        for(j=0; j<righe; j++){
                                if(matrice[j][i]==1) specie[j]=1;
                        }
                }
        }

//numero righe indotta
        for(i=0; i<righe; i++){
                if(specie[i]==1) righe_indotta++;
        }
//numero colonne indotta
        for(i=0; i<colonne; i++){
                if(caratteri[i]==1) colonne_indotta++;
        }

        corrispondenzaMC=new int [colonne_indotta];

//riempio matrice indotta
        matrice_indotta=new int*[righe_indotta];
        for(i=0; i<righe_indotta; i++){
                matrice_indotta[i]=new int [colonne_indotta];
        }
        i_indotta=0;
        j_indotta=0;
        for(i=0;i<righe; i++){
                if(specie[i]==1){
                        for(j=0; j<colonne; j++){
                                if(caratteri[j]==1){
                                        matrice_indotta[i_indotta][j_indotta]=matrice[i][j];
                                        corrispondenzaMC[j_indotta]=corrispondenza_cc[j];
                                        //aggiorno indici matrice indotta
                                        if(j_indotta!=colonne_indotta) j_indotta++;
                                        if((j_indotta==colonne_indotta)&&(i_indotta<righe_indotta)){
                                                i_indotta++;
                                                j_indotta=0;
                                        }
                                }
                        }
                }
        }
}

//verifico se s1 incluso in s2 (s1<s2)
int sIncluded(int** matrice, int colonne, int s1, int s2) {
        int i, k;
        for (i=0; i<colonne; i++){
                if ((matrice[s1][i]==1) & (matrice[s2][i]==0)){
                        return 0;
                }
        }
        return 1;
}
//conta il numero di 1 in una specie (riga)
int conta_uni(int** m, int riga, int colonne){
        int i,n;
        n=0;
        for(i=0; i<colonne; i++){
                if(m[riga][i]==1) n++;
        }
        return n;
}

int trova_sorgenti(int colonna, int righe){
        int i;
        if(specieRealizzate[colonna]==1) return 0;
        if(sorgenti_potenziali[colonna]==0) return 0;
        //verifico che specie non abbia archi entranti
        for (i=0; i<righe; i++){
                if(hasse[i][colonna]==1) return 0;
        }
        return 1;
}

int trova_sink(int riga, int righe){
        int i;
        //cout<<"trovo sink"<<endl;
        //se la specie è già stata realizzata
        if (specieRealizzate[riga]==1) return 0;
        for (i=0; i<righe; i++){
                if(hasse[riga][i]==1) return 0;
        }
        return 1;
}
//calcolo in-degree di un nodo (specie colonna in matrice Hesse)
int inDeg(int colonna, int righe){
        int i, deg;
        deg=0;
        for (i=0; i<righe; i++){
                if(hasse[i][colonna]==1) deg++;
        }
        return deg;
}

//calcolo out-degree di un nodo (specie riga in matrice Hesse)
int outDeg(int riga, int righe){
        int i, deg;
        deg=0;
        for (i=0; i<righe; i++){
                if(hasse[riga][i]==1) deg++;
        }
        return deg;
}

void aggiungi_nodo(int s, int righe){
        if(indice_path<righe) percorso[indice_path]=s;
        indice_path++;
}


int realizza_percorso(int** matrice, int righe, int colonne, int* percorso){
        int i,j, e,  cont_neri, cont_specie, cont, n_componenti;
        int** grb;
        int* c_universali;
        int* s_realizzate;
        int* c_attivi;
        int ammissibile;
        grb = (int **)calloc(righe, sizeof(int *));
        for (i = 0; i < righe; i++){
                grb[i] = (int *)calloc(colonne, sizeof(int));
        }

        for (i = 0; i < righe; i++) {
                for (j = 0; j < colonne; j++) {
                        grb[i][j]=matrice[i][j];

                }
        }

        c_universali=new int[colonne];
        for(i=0; i<colonne; i++){
                cont_neri=0;
                for(j=0; j<righe; j++){
                        if(grb[j][i]==1) {
                                cont_neri++;
                        }
                }
                if(cont_neri>0) c_universali[i]=0;
                if(cont_neri==0) c_universali[i]=1;
        }
        //specie realizzate: nessun arco entrante.
        s_realizzate=new int[righe];
        for(i=0; i<righe; i++){
                cont_specie=0;
                for(j=0; j<colonne; j++){
                        if(grb[i][j]!=0) {
                                cont_specie++;
                        }
                }
                if(cont_specie!=0) s_realizzate[i]=0;
                if(cont_specie==0) s_realizzate[i]=1;
        }

        //caratteri attivi: attivo se reso universale e NON connesso con archi rossi a tutte le specie della sua componente
        c_attivi=new int[colonne];
        for(i=0; i<colonne; i++) c_attivi[i]=0;
        for(i=0; i<colonne; i++){
                if (c_universali[i]==1){
                        cont=0;
                        for(j=0; j<righe; j++){
                                if(grb[j][i]==2) cont++;
                        }
                        if(cont==righe) c_attivi[i]=0;
                        if(cont<righe) c_attivi[i]=1;
                }
        }
        //leggo percorso da fine a inizio
        for(i=righe-1; i>-1; i--){
                //per ogni nodo del percorso, se nodo !=-1
                if(percorso[i]!=-1){
                        //realizza la specie
                        //realizza_specie(matrice,righe,colonne,percorso[i],s_realizzate, c_universali, c_attivi, grb, soluzione_massimali);
                        realizza_specie(grb,righe,colonne,percorso[i],s_realizzate, c_universali, c_attivi);
                }
        }
        ammissibile=1;
// verifico ammissibilità sink (percorso[0])
        n_componenti=calcola_componenti(grb,righe,colonne);
        if(n_componenti==-2)
                return 1; //grb formato da soli singoletti --> nessun conflitto!

        ConflictGraph cg (grb,righe,colonne);
        cg.print_graph();

        //per ogni coflitto, verifico se la coppia di caratteri appartiene al sink. In tal caso, sink non ammissibile
        for(e=0; e<cg.edges; e++){
                if(ammissibile==1){
                        if(matrice[percorso[0]][archi_gabry[e][0]]==1){
                                if(matrice[percorso[0]][archi_gabry[e][1]]==1){
                                        ammissibile=0;
                                }
                        }
                }
        }
        if(ammissibile==1){
                return 1;
        }
        else if (ammissibile==0) {
                return 0;
        }
        return -1;
}

void realizza_specie(int** Grb, int righe, int colonne, int specie, int* specie_realizzate, int* caratteri_universali, int* caratteri_attivi){
        int flag_realizzata;
        //per ogni carattere della specie non ancora universale, rend universale
        if(specie_realizzate[specie]==0){
                flag_realizzata=0;

                //per ogni carattere a 1 nella specie, se il carattere non è ancora stato reso universale rendilo universale

                while(flag_realizzata==0){
                        for(int i=0; i<colonne; i++){
                                if((Grb[specie][i]==1)&&(caratteri_universali[i]==0)){
                                        rendi_universale(Grb, righe, colonne, i,  caratteri_universali, caratteri_attivi, specie_realizzate);  //i: carattere da rendere universale

                                        if(specie_realizzata(Grb,righe,colonne,specie,caratteri_universali)) {
                                                //    cout<<"specie realizzata"<<endl;
                                                flag_realizzata=1;
                                        }
                                }

                                specie_realizzate[specie]=1;
                        }
                }
        }
}


void rendi_universale(int** Grb, int righe, int colonne, int i, int* caratteri_universali, int* caratteri_attivi, int* specie_realizzate){  //i: carattere da rendere universale
        int j;
        int tspecie[righe];
        int tcarattere[colonne];
        //il carattere da rendere universale diventa attivo
        caratteri_attivi[i]=1;

        caratteri_universali[i]=1;

        // calcolo componente connessa del carattere
        for(j=0; j<righe; j++) tspecie[j]=0;
        for(j=0; j<colonne; j++) tcarattere[j]=0;

        valuta_colonna(Grb, righe, colonne, i, tspecie, tcarattere);

        for (j=0; j<righe; j++){ //scorro le specie per vedere a cosa connettere il carattere
                if (Grb[j][i]==1){
                        Grb[j][i]=0; //cancello archi neri
                }
                else if (Grb[j][i]==0) {
                        //verifica che la specie appartiene alla componente di cui fa parte il carattere. Se appartiene metti un arco rosso

                        if ((tspecie[j]==1) && (specie_realizzate[j]==0)){
                                Grb[j][i]=2;    //arco rosso tra carattere e specie della componente connessa se specie non ancora realizzata
                        }
                }

        }


// aggiorna_caratteri_attivi(matrice, righe, colonne, caratteri_attivi, Grb, specie_realizzate);
        aggiorna_caratteri_attivi(Grb, righe, colonne, caratteri_attivi, specie_realizzate);
}

int valuta_colonna(int** Grb, int righe, int colonne, int carattere, int* tspecie, int* tcarattere){
        int i;
        for (i=0; i<righe; i++){
                //se il carattere è collegato alla specie con un arco nero o un arco rosso allora è connesso alla specie
                if ((Grb[i][carattere]==1) | (Grb[i][carattere]==2)){
                        if (tspecie[i]==0) {
                                tspecie[i]=1;
                                //printf("specie connessa al carattere %d: %d", carattere, i);
                                valuta_riga(Grb, righe, colonne, i, tspecie, tcarattere);
                        }
                }
        }
        return -1;
}

int valuta_riga(int** Grb, int righe, int colonne, int specie, int* tspecie, int* tcarattere){
        int j;
        //costruzione grafo connesso di "carattere"

        for (j=0; j<colonne; j++){
                if ((Grb[specie][j]==1) | (Grb[specie][j]==2)){
                        if (tcarattere[j]==0) {
                                tcarattere[j]=1;
                                valuta_colonna(Grb, righe, colonne, j, tspecie, tcarattere);
                        }
                }
        }
        return -1;
}

void aggiorna_caratteri_attivi(int** Grb, int righe, int colonne, int* caratteri_attivi, int* specie_realizzate){
        int i,j, specie,k,r;
        int flag;

        int tspecie[righe];
        int tcarattere[colonne];
        //per ogni carattere attivo
        for(i=0; i<colonne; i++){
                if(caratteri_attivi[i]==1){
                        flag=0;
                        // calcolo componente connessa del carattere
                        for(j=0; j<righe; j++) tspecie[j]=0;
                        for(j=0; j<colonne; j++) tcarattere[j]=0;
                        valuta_colonna(Grb, righe, colonne, i, tspecie, tcarattere);

                        //se carattere connesso con archi rossi a tutte le specie della sua componente, posso spegnerlo

                        for(k=0; k<righe; k++){
                                if((tspecie[k]==1) && (Grb[k][i]!=2)) flag=flag+1;
                        }
                        if (flag>0){
                                caratteri_attivi[i]=1;
                                //cout<<"non disattivo"<<endl;
                        }
                        // se disattivo un carattere, devo controllare le specie realizzate
                        if (flag==0) {
                                caratteri_attivi[i]=0;
                                //elimino carattere e relativi archi da grafo rb
                                for(specie=0; specie<righe; specie++) Grb[specie][i]=0;

                                aggiorna_specie_realizzate(Grb, righe, colonne, specie_realizzate);

                                aggiorna_caratteri_attivi(Grb, righe, colonne, caratteri_attivi, specie_realizzate);
                        }
                }
        }
}

void aggiorna_specie_realizzate(int** Grb, int righe, int colonne, int* specie_realizzate){
        int i,j;
        int archi;

        for(i=0; i<righe; i++){ //confronto ogni specie con il vettore di caratteri attivi relativi alla stessa componente della specie.

                //se la specie è già stata realizzata, vai avanti
                if(specie_realizzate[i]==0){
                        archi=0;
                        //controlla se ci sono archi entranti
                        for(j=0; j<colonne; j++){
                                if(Grb[i][j]!=0) archi=archi+1;
                        }
                        if (archi==0) {
                                specie_realizzate[i]=1;
                                specieRealizzate[i]=1;
                        }
                }
        }
}


int valuta_colonna(int** matrice, int righe, int colonne, int carattere, int** Grb, int* tspecie, int* tcarattere){
        int i;
        for (i=0; i<righe; i++){
                //se il carattere è collegato alla specie con un arco nero o un arco rosso allora è connesso alla specie
                if ((Grb[i][carattere]==1) | (Grb[i][carattere]==2)){
                        if (tspecie[i]==0) {
                                tspecie[i]=1;
                                valuta_riga(matrice, righe, colonne, i, Grb, tspecie, tcarattere);
                        }
                }
        }
        return -1;
}

int valuta_riga(int** matrice, int righe, int colonne, int specie, int** Grb, int* tspecie, int* tcarattere){
        int j;
        //costruzione grafo connesso di "carattere"

        for (j=0; j<colonne; j++){
                if ((Grb[specie][j]==1) | (Grb[specie][j]==2)){
                        if (tcarattere[j]==0) {
                                tcarattere[j]=1;
                                valuta_colonna(matrice, righe, colonne, j, Grb, tspecie, tcarattere);
                        }
                }
        }
        return -1;
}


bool specie_realizzata(int** matrice,int righe,int colonne,int specie, int* caratteri_universali){
        int i;

        for(i=0; i<colonne; i++){
                if((matrice[specie][i]==1)&&(caratteri_universali[i]==0)) {
                        return false;
                }
        }
        return true;
}

//verifico se s1<s2
int included(int** matrice, int righe, int colonne, int s1, int s2){
        int i;
        for(i=0; i<colonne; i++){
                if((matrice[s1][i]==1)&&(matrice[s2][i]==0)) return 0;
        }
        return 1;
}

void estendi(int carattere, int** Grb){

        int i;
        for (i=0; i<righeO; i++){
                if (matriceO[i][carattere]==1) {
                        estesa[i][2*carattere]=1;
                        estesa[i][2*carattere+1]=0;
                }

                if (matriceO[i][carattere]==0) {
                        if (Grb[i][carattere]==0) {
                                estesa[i][2*carattere]=0;
                                estesa[i][2*carattere+1]=0;
                        }

                        if (Grb[i][carattere]==2) {
                                estesa[i][2*carattere]=1;
                                estesa[i][2*carattere+1]=1;
                        }
                }
        }
}

//Inverto ordine nodi percorso. es in:123-1   out: 321-1
int* riordina_percorso(int* percorso, int righe){
        int i, nodi;
        int* ordinato;

        ordinato=new int[righe];
        for(i=0; i<righe; i++) ordinato[i]=-1;
        nodi=0;
        for(i=0; i<righe; i++){
                if(percorso[i]!=-1) nodi++;
        }
        for(i=0; i<nodi; i++) ordinato[i]=percorso[nodi-1-i];
        return ordinato;
}

// verifico se il carattere "carattere" appartiene alla specie "specie"
int appartiene(int carattere, int specie){
        if (matriceO[specie][carattere]==1) return 1;
        return 0;
}

//verifica se c  con un carattere A già nella soluzione induce le configurazioni (0,1) (1,0) (1,1) nella matrice M
int conflitto(int c){
        int i,k, flag1, flag2, flag3;

        for(i=0; i<colonneO; i++){
                if(inserito(i)==1){
                        flag1=0;
                        flag2=0;
                        flag3=0;
                        for (k = 0; k < righeO; k++) {
                                if ((matriceO[k][i] == 1 ) && (matriceO[k][c] == 1)) flag1 = 1;
                                if ((matriceO[k][i] == 0) && (matriceO[k][c] == 1)) flag2 = 1;
                                if (((matriceO[k][i] == 1)) && (matriceO[k][c] == 0)) flag3 = 1;
                        }
                        if (flag1 && flag2 && flag3)  return 1;
                }
        }
        return 0;
}

//verifica se un carattere è già stato inserito nella soluzione
int inserito(int c){
        int i;

        for(i=0; i<colonneO; i++){
                if(soluzione[i]==c) return 1;
        }
        return 0;
}

//elimina eventuali righe uguali
void compattaIndottaMassimali(){
        int i,j, nr, i_matrice;
        int copia[righe_indotta];
        for(i=0; i<righe_indotta; i++) copia[i]=-1;
        nr=0;

        //calcola le righe diverse
        copia[0]=0;
        nr++;
        for(i=1; i<righe_indotta; i++){
                if(specieDiversa(i)==1){
                        copia[i]=0;
                        nr++;
                }
        }
        righeMC=nr;

        colonneMC=colonne_indotta;

        matriceMC=new int*[righeMC];
        for(i=0; i<righeMC; i++){
                matriceMC[i]=new int [colonneMC];
        }
        //riempio la matrice
        i_matrice=0;
        for(i=0; i<righe_indotta; i++){
                if(copia[i]==0){
                        for(j=0; j<colonneMC; j++){
                                matriceMC[i_matrice][j]=matrice_indotta[i][j];
                        }
                        i_matrice++;
                }

        }
}

//verifica se la specie s è diversa da tutte le specie che la precedono
int specieDiversa(int s){
        int i;
        int cont; //conta le uguaglianze
        cont=0;
        for(i=0; i<s; i++){ //per ogni specie i che precede la specie s
                if(specieUguali(i,s)) cont++;
        }
        if(cont>0) return 0;
        else return 1;
}

int specieUguali(int s1, int s2){
        int i;
        for(i=0; i<colonne_indotta; i++)
                if(matrice_indotta[s1][i]!=matrice_indotta[s2][i]) return 0;
        return 1;
}

int* costruiscoPercorso(int** matrice, int** hasse, int righe, int colonne, int source, int sink){
        int i;
        int* percorso;

        percorso=new int[righe];
        for(i=0; i<righe; i++) percorso[i]=-1;

        i=0;
        percorso[i]=source;

        while(percorso[i]!=sink){
                i++;
                percorso[i]=trovaSuccessivo(matrice, hasse, righe, colonne, percorso[i-1], sink);
        }
        return percorso;
}


int trovaSuccessivo(int** matrice, int** hasse, int righe, int colonne, int nodo, int sink){
        int i;

        for(i=0; i<righe; i++){
                if(hasse[nodo][i]==1){ //se specie i è collegata al nodo precedente
                        if(included(matrice, righe, colonne, i, sink)) //se specie i è inclusa nel sink
                                return i;
                }
        }
        return -1;
}

//prende una matrice, ne calcola le c.c. e su ogni componente richiama la procedura per risolvere la singola componente
void riduciMatrice(int** GRB, int righe, int colonne){
        int n_componenti, i, j;
        int cont;

        // DEBUG
        // printMatrix(GRB, righeO, colonneO);

// calcola le componenti connesse del grafo rosso nero
        cout << "RM1 " ;
        n_componenti=calcola_componenti(GRB,righe,colonne);
        cout << "RM2: " <<  n_componenti << endl;

        // per ogni componente GRB connessa
        for(int contatore_componente=0; contatore_componente<=n_componenti; contatore_componente++){
                // calcola matrice indotta dalla componente connessa di Grb
                cout << "Componente connessa" << endl;
                indotta_cc(contatore_componente);
                int universali[colonne_cc];
                for (i = 0; i < colonne_cc; i++)
                        universali[i] = 0;

                for(i=0; i<colonne_cc; i++){
                        cont=0;
                        for(j=0; j<righe_cc; j++){
                                if(matrice_cc[j][i]==2) cont++;
                        }
                        if(cont>0) universali[i]=1;
                }
                // calcola i caratteri massimali
                calcola_massimali(colonne_cc, universali, matrice_cc, righe_cc, specie_realizzate);
                // Calcolo la matrice indotta da soli massimali
                indotta_massimali(matrice_cc,righe_cc,colonne_cc,massimali);

                compattaIndottaMassimali();
                cout << "Calcola soluzione" << endl;
                calcolaSoluzione(matriceMC, righeMC, colonneMC);
        }
        //controllo se tutti i caratteri sono stati resi universali. Se non è così, richiamo l'algoritmo ricorsivamente
        int somma=0;
        for(i=0; i<colonneO; i++) somma=somma+car_universali[i];
        if(somma!=colonneO) {
                riduciMatrice(GRB, righeO, colonneO);
        }
}

void trovaPercorsi(int** matrice, int** hasse, int righe, int colonne){ //matrice di soli massimali
        int** percorsi;
        int* safe;
        int* percorsoOrdinato;
        int numeroPercorso;
        int i,j,k, nSo, nSi, ii, jj;
        int cont_neri, cont_specie, cont;
        int stop;
        nSo=0;
        nSi=0;
        sorgenti=new int[righe];
        sorgenti_potenziali=new int[righe];
        sink=new int[righe];
        in_deg=new int[righe];
        specieRealizzate=new int[righe];
        for(i=0; i<righe; i++) sorgenti_potenziali[i]=1; //inizialmente suppongo che qualsiasi nodo possa essere sorgente
        for(i=0; i<righe; i++) specieRealizzate[i]=0;
//SISTEMARE CONDIZIONE ITERAZIONE: CONTROLLO SU GC MASSIMALI

        for(i=0; i<righe; i++){
                sorgenti[i]=trova_sorgenti(i,righe);
                sink[i]=trova_sink(i,righe);
                in_deg[i]=inDeg(i,righe);
        }
        for(i=0; i<righe; i++){
                if (sorgenti[i]==1){
                        nSo++;
                }
        }

        for(i=0; i<righe; i++){
                if (sink[i]==1) {
                        nSi++;
                }
        }

        //inizializzo matrice percorsi: al max numero percorsi= numero sources*numero sink
        percorsi=new int*[nSo*nSi];
        for(i=0; i<(nSo*nSi); i++){
                percorsi[i]=new int [righe]; //ogni percorso è al massimo la lista di tutte le specie della matrice
        }
        for(i=0; i<nSo*nSi; i++){
                for(j=0; j<righe; j++)
                        percorsi[i][j]=-1;
        }

        numeroPercorso=0;

        for(i=0; i<righe; i++){
                if(sorgenti[i]==1){
                        for(j=0; j<righe; j++){
                                if(sink[j]==1){
                                        if(included(matrice, righe, colonne, i,j)){
                                                // cout<<"costruisco percorso tra "<<i<<j<<endl;
                                                percorsi[numeroPercorso] = costruiscoPercorso(matrice, hasse, righe, colonne, i, j);
                                                numeroPercorso++;
                                        }
                                }
                        }
                }
        }

        //determino quali percorsi sono safe
        safe=new int[nSo*nSi];
        percorsoOrdinato=new int[righe];
        for(i=0; i<righe; i++)percorsoOrdinato[i]=-1;
        for(i=0; i<nSo*nSi; i++) safe[i]=-1;
        stop=0;
        for(i=0; i<nSo*nSi; i++){
                if(stop==0){    //se non ho ancora trovato un percorso valido
                        if(percorsi[i][0]!=-1){
                                percorsoOrdinato=riordina_percorso(percorsi[i], righe); //inverto ordine dei nodi
                                safe[i]=realizza_percorso(matrice, righe, colonne, percorsoOrdinato);
                                if(safe[i]==1){
                                        stop=1; //devo passare al passo ricorsivo, non vado avanti con altri possibili percorsi safe
                                                //1- prendo la sorgente del percorso
                                                //      cout<<"realizzo la sorgente safe "<<percorsi[i][0]<<endl;
                                                //2- copio nella soluzione generale la sequenza di caratteri per realizzare la sorgente
                                                //determino indice da cui iniziare a copiare
                                        k=determinaIndice(soluzione);
                                        //copio caratteri, in base alla tabella di associazione originale-indotto
                                        copiaSoluzione(soluzione,k,percorsi[i][0], matrice, colonne);

                                        //3- realizzo i caratteri della sorgente nel grb della soluzione1 o della soluzione2
                                        for(ii=0; ii<colonneO; ii++){
                                                cont_neri=0;
                                                for(jj=0; jj<righeO; jj++){
                                                        if(GRB[jj][ii]==1) {
                                                                cont_neri++;
                                                        }
                                                }

                                                if(cont_neri>0) car_universali[ii]=0;
                                                if(cont_neri==0) car_universali[ii]=1;
                                        }

                                        //specie realizzate: nessun arco entrante.
                                        for(ii=0; ii<righeO; ii++){
                                                cont_specie=0;
                                                for(jj=0; jj<colonneO; jj++){
                                                        if(GRB[ii][jj]!=0) {
                                                                cont_specie++;
                                                        }
                                                }
                                                if(cont_specie!=0) specie_realizzate[ii]=0;
                                                if(cont_specie==0) specie_realizzate[ii]=1;
                                        }
                                        //caratteri attivi: attivo se reso universale e NON connesso con archi rossi a tutte le specie della sua componente
                                        for(ii=0; ii<colonneO; ii++){
                                                if (car_universali[ii]==1){
                                                        cont=0;
                                                        for(jj=0; jj<righeO; jj++){
                                                                if(GRB[jj][ii]==2) cont++;
                                                        }
                                                        if(cont==righeO) car_attivi[ii]=0;
                                                        if(cont<righeO) car_attivi[ii]=1;
                                                }
                                        }
                                        aggiornaGRB(GRB,righeO,colonneO, k,specie_realizzate, car_universali, car_attivi);

                                        //4- richiamo l'algoritmo sul grb generale 1 o 2
                                }
                        }
                }
        }
}

//determino l'indice da dove iniziare a copiare l'ordine di caratteri della soluzione
int determinaIndice(int* soluzione){
        int i;
        for(i=0; i<colonneO; i++){
                if(soluzione[i]==-1) return i;
        }
}

//aggiorna la soluzione con i caratteri della sorgente da realizzare
void copiaSoluzione(int* soluzione,int indice,int specie, int** matrice, int colonne){  //matrice di soli massimali
        int i;
        for(i=0; i<colonne; i++){
                if(matrice[specie][i]==1) {
                        soluzione[indice]=corrispondenzaMC[i];
                        indice++;
                }
        }
}

void aggiornaGRB(int** Grb,int righeO,int colonneO,int k,int* specie_realizzate,int* car_universali, int* car_attivi){
        int i;
        //per ogni carattere della specie non ancora universale, rend universale
        for(i=k; i<colonneO; i++){
                if(soluzione[i]!=-1){
                        rendi_universale(Grb, righeO, colonneO, soluzione[i], car_universali, car_attivi, specie_realizzate);  //i: carattere da rendere universale
                        estendi(soluzione[i], Grb);

                }
        }
}

// verifica se tra le due colonne esiste la sottomatrice proibita
// restituisce 0 se esiste la sottomatrice proibita, 1 se non esiste

int sottomatriceProibita(int ** a, int c1, int c2) {

        int i;

        int flag1, flag2, flag3;
        flag1 = flag2 = flag3 = 0;

        for (i = 0; i < righeO; i++) {
                if ((a[i][c1] == 0 ) && (a[i][c2] == 1)) {
                        flag1 = 1;
                }
                if ((a[i][c1] == 1 ) && (a[i][c2] == 0)) {
                        flag2 = 1;
                }
                if ((a[i][c1] == 1 ) && (a[i][c2] == 1)) {
                        flag3 = 1;
                }
        }
        if (flag1 && flag2 && flag3) return 1; //esiste sottomatrice proibita
        else
                return 0;  //non esiste sottomatrice proibita
}
