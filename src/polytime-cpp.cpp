/*
  Copyright Gabriella Trucco 2015-2016
*/

// TODO: check global var specieRealizzate
// go to the next solution, if it is not solution for the first graph

#include<stdlib.h>
#include<stdio.h>
#include <iostream>
#include <fstream>
#include <assert.h>
#include <vector>
#include <algorithm> // for copy
#include <iterator> // for ostream_iterator
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
int componenti_matrice;
int contatore_componente;
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
//      bool connesso(int componente);
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

        // Destructor
        //~ConflictGraph ();


        int** cgraph;                   // another representation of the conflict graph in which the arcs are indexed
        int edges;                              // number of edges in the graph

        int* species_sequence;          // S_q, i.e., le specie in S* ordinate a seconda del numero di 1

        //char* mapping_chars;  // serve per fare in modo che i caratteri siano indicizzati con lettere dell'alfabeto e non con interi

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
        //cout<<"Costruisco grafo dei conflitti"<<endl;

        for (i = 0; i < get_vertex(); i++) {
                if(carattere_connesso(m, righe, i)){
                        for (j = i + 1; j < get_vertex(); j++) {
                                if(carattere_connesso(m, righe, j)){
                                        //cout<<i<<j<<endl;
                                        if (red_conflict(m, righe, colonne, i, j) == true) {
                                                // cout<<"conflitto;"<<endl;
                                                insert_edge(i, j);                                              // add the arc in the adjunct list
                                                cgraph[i][j] = cgraph[j][i] = ++edges;  // add the arc in the adjunct matrix
                                        }
                                }
                        }
                }
        }

//      cout<<"numero di archi: "<<edges<<endl;
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
                //      if (t == NULL) cout << mapping_chars[i] << endl;        // it prints also singletons (i.e., unconnected vertexes)
                while (t != NULL) {
                        if (i < t->value) {
                                archi_gabry[x][0]= i;
                                archi_gabry[x][1]=t->value;
                                x++;
                        }
                        t = t->next;
                }
        }
        /*  cout<<"archi gabry:"<<endl;
            for(i=0; i<edges;i++){
            for(j=0; j<2; j++)
            cout<<archi_gabry[i][j];
            cout<<endl;
            }*/
}

// A method to insert a new arc in the graph between the vertex of character i and the vertex of character j
int ConflictGraph::insert_edge(int i, int j) {

        //cout<<"contatore archi: "<<contatore_archi<<endl;
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

        int flag1, flag2, flag3, flag4;
        int flag5, flag6, flag7;
        flag1 = flag2 = flag3 = flag4 =0;
        flag5 = flag6 = flag7=0;
        //cout<<"cerco conflitto tra caratteri "<<i<<" "<<j<<endl;

// controllo che i due caratteri appartengono alla stessa componente e che le specie considerate non siano ancora state realizzate
        if (comp_colonne[i]==comp_colonne[j]){
                // cout<<"Stessa componente"<<endl;
                for (k = 0; k < righe; k++) {
                        if(specie_non_realizzata(m,colonne,k)){

                                /*  if ((matrice[k][i] == 0 ) & (matrice[k][j] == 0) & (comp_righe[k]==comp_colonne[i])) flag1 = 1;
                                    if ((matrice[k][i] == 0) & (matrice[k][j] == 1) & (comp_righe[k]==comp_colonne[i])) flag2 = 1;
                                    if (((matrice[k][i] == 1)) & (matrice[k][j] == 0) & (comp_righe[k]==comp_colonne[i])) flag3 = 1;
                                    if ((matrice[k][i] == 1) & (matrice[k][j] == 1) & (comp_righe[k]==comp_colonne[i])) flag4 = 1;*/
                                if ((m[k][i] == 0 ) & (m[k][j] == 0) & (comp_righe[k]==comp_colonne[i])) flag1 = 1;
                                if ((m[k][i] == 0) & (m[k][j] == 1) & (comp_righe[k]==comp_colonne[i])) flag2 = 1;
                                if ((m[k][i] == 0) & (m[k][j] == 2) & (comp_righe[k]==comp_colonne[i])) flag5 = 1;
                                if (((m[k][i] == 1)) & (m[k][j] == 0) & (comp_righe[k]==comp_colonne[i])) flag3 = 1;
                                if (((m[k][i] == 2)) & (m[k][j] == 0) & (comp_righe[k]==comp_colonne[i])) flag6 = 1;
                                if ((m[k][i] == 1) & (m[k][j] == 1) & (comp_righe[k]==comp_colonne[i])) flag4 = 1;
                                if ((m[k][i] == 2) & (m[k][j] == 2) & (comp_righe[k]==comp_colonne[i])) flag7 = 1;
                        }
                }
        }
        if (flag1 & flag2 & flag3 & flag4) return true; //sigma nero
        if (flag5 & flag6 & flag7) return true; //sigma rosso
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
        int i;
        link t;

        // print the first representation of the graph
        // the arcs and the singletons
        for (i = 0; i < get_vertex(); i++) {
                t = adj[i];
                if (t == NULL) cout << mapping_chars[i] << endl;        // it prints also singletons (i.e., unconnected vertexes)
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
                //cout << "Dimensione della componente non banale: " << size << endl;
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
        //cout<<"qui";
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

        //cout << "Valore di i: " << i << endl;
        //cout << "valore di get_vertex: " << get_vertex()<< endl;
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
void realizza_specie(int** Grb, int righe, int colonne, int specie, int* specie_realizzate, int* caratteri_universali, int* caratteri_attivi);
void rendi_universale(int** Grb, int righe, int colonne, int i, int* caratteri_universali, int* caratteri_attivi, int* specie_realizzate, int flag);  //i: carattere da rendere universale
int valuta_colonna(int** Grb, int righe, int colonne, int carattere, int* tspecie, int* tcarattere);
int valuta_riga(int** Grb, int righe, int colonne, int specie, int* tspecie, int* tcarattere);
void aggiorna_caratteri_attivi(int** Grb, int righe, int colonne, int* caratteri_attivi, int* specie_realizzate);
void aggiorna_specie_realizzate(int** Grb, int righe, int colonne, int* specie_realizzate);
int valuta_colonna(int** matrice, int righe, int colonne, int carattere, int** Grb, int* tspecie, int* tcarattere);
int valuta_riga(int** matrice, int righe, int colonne, int specie, int** Grb, int* tspecie, int* tcarattere);
void aggiorna_caratteri_attivi(int** matrice, int righe, int colonne, int* caratteri_attivi, int** Grb, int* specie_realizzate);
void aggiorna_specie_realizzate(int** matrice, int righe, int colonne, int* specie_realizzate, int** Grb);
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
int realizza_percorso(int** matrice, int righe, int colonne, int* percorso);
int* riordina_percorso(int* percorso, int righe);
void zigzagPath(int righe);
void percorriZigzag();
void alberoMassimali();
void calcolaSoluzione(int** matrice, int righe, int colonne, int* componentiRiga);
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
void riduciMatrice();
void trovaPercorsi(int** matrice, int** hasse, int righe, int colonne, int* componentiRiga);
int determinaIndice(int* soluzione);
void copiaSoluzione(int* soluzione,int indice,int specie, int** matrice, int colonne);
void aggiornaGRB(int k,int* specie_realizzate,int* car_universali, int* car_attivi);
int inclusioneCaratteri(int c1, int c2, int** matrice, int righe);
bool colonnaSingoletto(int** matrice,int righe,int colonna);
bool rigaSingoletto(int** matrice,int colonne,int riga);
bool soloSingoletti(int* componenti, int colonne);
int sottomatriceProibita(int ** a, int c1, int c2);
int specieMatrice(int specie, int** matrice, int colonne, int* componentiRiga);
int uguali(int** matrice, int righe, int c1, int c2);
int specieUguali(int* s1, int* s2, int colonne);
int universale(int carattere, int* componentiRiga);
int VerificaSafeInGRB(int** matrice, int righe, int colonne, int specie);
int sigmaRossi(int** matrice, int righe, int colonne);
/////////////////////////////////////////////////////////////////////////////////////////////////////////////


int main(int argc, char *argv[]) {
        int i,j,ii,jj;
        char a = 'a';
        char* fileName;
//flag_ammissibile=1;
//flag_hasse_vuoto=0;

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

                //inizializzo l'estesa con la coppia 10 per ogni 1 della matrice in ingresso
                for (i = 0; i < righeO; i++) {
                        for (j = 0; j < colonneO; j++) {
                                if(matriceO[i][j]==1){
                                        estesa[i][2*j]=1;
                                        estesa[i][2*j+1]=0;
                                }
                        }
                }

                //calcolo le componenti e richiamo algo di riduzione su ogni componente
                riduciMatrice();

                cout<<"SOLUZIONE: ";
                for(ii=0; ii<colonneO; ii++) cout<<soluzione[ii]<<" ";
                cout<<endl;

                //completo la matrice estesa con le coppie 00
                for (i = 0; i < righeO; i++) {
                        for (j = 0; j < 2*colonneO; j++) {
                                if(estesa[i][j]==-1)  estesa[i][j]=0;
                        }
                }

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
void calcolaSoluzione(int**matrice, int righe, int colonne, int*componentiRiga){
        int i,j,k;

        /*    cout<<"componenti righe dentro calcolaSoluzione: ";
              for(i=0; i<righeO; i++) cout<<componentiRiga[i];
              cout<<endl;
        */
//cout<<"GRB in calcolaSoluzione"<<endl;
//printMatrix(GRB, righeO, colonneO);

//nsoluzione=0;
//non solo massimali, ma generale

/*soluzioneMassimali=new int*[10];  //DA RENDERE PARAMETRICO IN BASE AL NUMERO DI SOLUZIONI DI MASSIMALI
  for (i = 0; i < 10; i++){
  soluzioneMassimali[i] = new int[colonne];
  }
  for (i = 0; i < 10; i++) {
  for (j = 0; j < colonne; j++) {
  soluzioneMassimali[i][j] = -1;
  }
  }*/

//int* specie_realizzate;
        int n_uni;
//    CarUniversali=new int[colonne];
//for(i=0; i<colonne; i++) CarUniversali[i]=0;




//S_Realizzate=new int[righe];
//for(i=0; i<righe; i++) S_Realizzate[i]=0;

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
/* cout<<"Inclusioni:"<<endl;
   for(i=0; i<righe; i++){
   for(j=0; j<righe; j++){
   cout<<inclusioni[i][j];
   }
   cout<<endl;
   }*/

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
                        //  cout<<"riga "<<i<<" con numero di 1 minore di 2"<<endl;
                        for(j=0; j<righe; j++) hasse[i][j]=inclusioni[i][j];
                }
                else{
                        // cout<<"verifica archi per specie "<<i<<endl;
                        for(j=0; j<righe-1; j++){
                                if(inclusioni[i][j]==1){
                                        for(k=j+1; k<righe; k++){
                                                if(inclusioni[i][k]==1){
                                                        if((inclusioni[j][k]==1)|(inclusioni[k][j]==1)){
                                                                //cout<<"specie "<<j<<" "<<k<<" in inclusione tra loro"<<endl;
                                                                if(inclusioni[j][k]==1) hasse[i][k]=0;
                                                                else hasse[i][j]=0;
                                                        }
                                                }
                                        }
                                }
                        }
                }
        }
        /*cout<<"Hasse:"<<endl;
          for(i=0; i<righe; i++){
          for(j=0; j<righe; j++){
          cout<<hasse[i][j];
          }
          cout<<endl;
          }*/

//trovaSorgenti(matrice, hasse, righe, colonne);

        trovaPercorsi(matrice, hasse, righe, colonne, componentiRiga);


}


void readMatrix(int** matrice, int righe, int colonne) {
        int i,j;

        for (i = 0; i < righe; i++) {
                for (j = 0; j < colonne; j++) {
                        fscanf(file, "%d", &(matrice[i][j]));
                }
        }

}

void print_array(int * arr, int len, std::string label) {
        cout << label << " ";
        for (int i = 0; i < len; i++)
                cout << " " << arr[i];

        cout << endl;
}


// Overload << for vectors
template <typename T>
std::ostream& operator<< (std::ostream& out, const std::vector<T>& vec) {
        if ( !vec.empty() ) {
                out << '[';
                std::copy (vec.begin(), vec.end(), std::ostream_iterator<T>(out, ", "));
                out << "]";
        }
        return out;
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

   Moreover singolettiColonna and singolettiRiga are set to 1 iff the column/row is a singleton in the red-black graph
*/
int calcola_componenti(int** matrice, int righe, int colonne){
        int i,j;
        assert(righe > 0);
        assert(colonne > 0);

        comp_colonne = new int [colonne];
        for(i=0; i<colonne; i++)
                comp_colonne[i]=-1;
        comp_righe = new int [righe];
        for(i=0; i<righe; i++)
                comp_righe[i]=-1;

        bool checked[righe+colonne+1];
        bool reached[righe+colonne+1];
        checked[righe+colonne] = true; // sentinel
        reached[righe+colonne] = true; // sentinel
        int num_connected_components = -2;

//        Consider only nontrivial connected components
        for(i=0; i<colonne; i++)
                if(colonnaSingoletto(matrice, righe, i)) {
                        // cout<<"colonna "<<i<<"singoletto"<<endl;
                        comp_colonne[i]=-2;
                        checked[righe+i] = true;
                        reached[righe+i] = true;
                } else {
                        comp_colonne[i] = -1;
                        checked[righe+i] = false;
                        reached[righe+i] = false;
                }

        for(i=0; i<righe; i++)
                if(rigaSingoletto(matrice, colonne, i)) {
                        comp_righe[i]=-2;
                        checked[i] = true;
                        reached[i] = true;
                } else {
                        comp_righe[i] = -1;
                        checked[i] = false;
                        reached[i] = false;
                }
        /*  cout << "raw COMP colonne" << endl;
            for(i=0; i<colonne; i++)
            cout<<comp_colonne[i]<<" ";
            cout<<endl;
            cout << "raw COMP righe" << endl;
            for(i=0; i<righe; i++)
            cout<<comp_righe[i]<<" ";
            cout<<endl;
            cout << "reached:";
            for(i=0; i<righe+colonne; i++)
            cout<<reached[i]<<" ";
            cout<<endl;
            cout << "checked:";
            for(i=0; i<righe+colonne; i++)
            cout<<checked[i]<<" ";
            cout<<endl;*/
        bool all_singletons = true;
        //        Compute connected components
        for(int current = 0, component_id=0; current < righe + colonne ; component_id++) {
                /* find the first vertex of the new connected component */
                for (current = 0; checked[current]; current++) {}
                //  cout << "current:" << current << all_singletons << endl;
                if (current < righe + colonne)
                        all_singletons = false;
                reached[current ] = true;

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
                        if (checked[current] && comp_righe[current] == -1)
                                comp_righe[current] = component_id;
                        if (!checked[current])
                                source_new_component = current;
                }
                for (current=0; current < colonne; current++) {
                        if (checked[righe+current] && comp_colonne[current] == -1)
                                comp_colonne[current] = component_id;
                        if (!checked[righe+current])
                                source_new_component = current;
                }
                current = source_new_component;
                num_connected_components = component_id;
        }

        print_array(comp_colonne, colonne, "COMP colonne");
        print_array(comp_righe, righe, "COMP righe");
        cout << num_connected_components << all_singletons << endl;

/* If there are only singletons, return -2 */
        return (all_singletons) ? -2 : num_connected_components;
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


void calcola_massimali(int colonne, int* caratteri_universali, int** matrice, int righe, int* specie_realizzate){
        massimali = (int *) calloc(colonne, sizeof(int));
        for (auto i = 0; i < colonne; i++)
                massimali[i] = 0;

        for(auto i=0; i<colonne; i++){
                if(caratteri_universali[i]==0){ //il carattere deve ancora essere realizzato
                        // cout<<"verifico se carattere "<<i<<" massimale_______________________________________________"<<endl;

                        // cout<<i<<" deve ancora essere realizzato"<<endl;
                        //il carattere non deve essere incluso in uno degli altri caratteri non ancora resi universali
                        //oppure deve essere l'ultimo da rendere universale
                        if((!(incluso(i, caratteri_universali, righe, specie_realizzate, matrice, colonne))) || (ultimo_carattere(i, colonne, caratteri_universali))){
                                // cout<<i<<" massimale"<<endl;
                                massimali[i]=1;
                        }
                }
                //  else cout<<"carattere già realizzato"<<endl;
        }
        if(no_massimali(massimali, colonne)){ //non ho trovato massimali con il blocco precedente ma ci sono ancora caratteri da realizzare
                // i rimanenti caratteri sono tutti massimali - dovrebbero essere uguali tra loro
                for(auto i=0; i<colonne; i++){
                        if(caratteri_universali[i]==0)
                                massimali[i]=1;
                }
        }
        /*   cout<<"Insieme di massimali: ";
             for(i=0; i<colonne; i++) {
             cout<<massimali[i];
             }
             cout<<endl;*/
}

//stabilisco se il carattere c è incluso in un altro carattere
int incluso(int c, int* caratteri_universali, int righe, int* specie_realizzate, int** matrice, int colonne){
        int i;
        int incluso; //se 0: non incluso; se >0, incluso
        // cout<<"--------------------------------------------------------------------------------"<<endl;
        // cout<<"verifico inclusione carattere "<<c<<endl;
        incluso=0; //ipotizzo inizialmente non sia incluso
        // cout<<"verifico se carattere "<<c<<" incluso in altri caratteri"<<endl;
        for(i=0; i<colonne; i++){
                // if((i!=c)&(caratteri_universali[i]==0)){
                if((i!=c)){
                        if(caratteri_universali[i]==0){
                                //     cout<<"confronto con carattere "<<i<<endl;
                                if(uguali(matrice, righe, i, c)) {
                                        //       cout<<"i due caratteri sono uguali --> non incluso"<<endl;
                                        incluso=incluso+0;
                                }
                                else incluso=incluso + inclusioneCaratteri(c,i, matrice, righe);
                        }
                }
        }
        // cout<<"numero inclusioni di carattere "<<c<<": "<<incluso<<endl;
        if (incluso==0) return 0;
        else return 1;
}

//verifica se due colonne sono uguali
int uguali(int** matrice, int righe, int c1, int c2){
        int i;
        for(i=0; i<righe; i++){
                if (matrice[i][c1]!=matrice[i][c2]) return 0;
        }
        return 1;
}

//verifico se carattere c1 incluso in carattere c2
int inclusioneCaratteri(int c1, int c2, int** matrice, int righe){
        int i;

        for(i=0; i<righe; i++){
                if((matrice[i][c1]==1) & (matrice[i][c2]==0)) {
                        //  cout<<c1<<" NON incluso in "<<c2<<endl;
                        return 0;
                }
        }
//cout<<c1<<" incluso in "<<c2<<endl;
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
        // cout<<"ultimo carattere da rendere universale"<<endl;
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
        int righe_indotta=0;
        int colonne_indotta=0;
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
//cout<<righe_cc<<colonne_cc<<endl;

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
                                        if((j_cc==colonne_cc)&(i_cc<righe_cc)){
                                                i_cc++;
                                                j_cc=0;
                                        }
                                }
                        }
                }
        }
}

void indotta_massimali(int**matrice, int righe, int colonne, int* massimali){
        int* caratteri;
        int* specie;
        int i,j;
        int i_indotta, j_indotta;

        righe_indotta=0;
        colonne_indotta=0;

        caratteri = (int *) calloc(colonne, sizeof(int));
        for (i = 0; i < colonne; i++) caratteri[i] = 0;

        specie = (int *) calloc(righe, sizeof(int));
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
        for (auto i=0; i<colonne; i++){
                if ((matrice[s1][i]==1) & (matrice[s2][i]==0)){
                        //   cout<<"non incluso "<<endl;
                        return 0;
                }
        }
        //  cout<<"incluso "<<endl;
        //  cout<<endl;
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


//verifico su grb di soli massimali
int realizza_percorso(int** matrice, int righe, int colonne, int* percorso){
        int i,j, e, cont_neri, cont_specie, cont, n_componenti;
        int** grb;
        int* c_universali;
        int* s_realizzate;
        int* c_attivi;
        int ammissibile;
        int* soluzione_massimali;
//cout<<"dentro la realizzazione del percorso"<<endl;
//cout<<"matrice:"<<endl;
//        printMatrix(matrice, righe, colonne);

        //  cout<<"mmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm"<<righe<<colonne<<endl;

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
                        cout<<"realizzo la specie "<<percorso[i]<<endl;
                        //realizza_specie(matrice,righe,colonne,percorso[i],s_realizzate, c_universali, c_attivi, grb, soluzione_massimali);
                        realizza_specie(grb,righe,colonne,percorso[i],s_realizzate, c_universali, c_attivi);
                }
        }
        ammissibile=1;
//cout<<"vvvvvvvvvvvvvvvvvvvvvvv"<<endl;
// verifico ammissibilità sink (percorso[0])
//cout<<righe<<colonne<<endl;
        n_componenti=calcola_componenti(grb,righe,colonne);
        if(n_componenti==-2) return 1; //grb formato da soli singoletti --> nessun conflitto!

        ConflictGraph cg (grb,righe,colonne);
        //  cout<<"qui"<<endl;
        // cg.print_graph();

        //per ogni coflitto, verifico se la coppia di caratteri appartiene al sink. In tal caso, sink non ammissibile
        for(e=0; e<cg.edges; e++){
                if(ammissibile==1){
                        if(matrice[percorso[0]][archi_gabry[e][0]]==1){
                                if(matrice[percorso[0]][archi_gabry[e][1]]==1){
                                        // cout<<"conflitto tra i caratteri "<<archi_gabry[e][0]<<archi_gabry[e][1]<<endl;
                                        ammissibile=0;
                                }
                        }
                }
        }
        if(ammissibile==1){
                //  cout<<"Percorso ammissibile!"<<endl;
                delete[] c_universali;
                delete[] s_realizzate;
                delete[] c_attivi;
                return 1;
        }
        else if (ammissibile==0) {
                //  cout<<"Percorso NON ammissibile!"<<endl;
                delete[] c_universali;
                delete[] s_realizzate;
                delete[] c_attivi;
                return 0;
        }
}


void realizza_specie(int** Grb, int righe, int colonne, int specie, int* specie_realizzate, int* caratteri_universali, int* caratteri_attivi){
        int i;
        int flag_realizzata;
        //per ogni carattere della specie non ancora universale, rend universale
//cout<<"........................"<<endl;
        if(specie_realizzate[specie]==0){
                flag_realizzata=0;

                //per ogni carattere a 1 nella specie, se il carattere non è ancora stato reso universale rendilo universale

                while(flag_realizzata==0){
                        for(i=0; i<colonne; i++){
                                if((Grb[specie][i]==1)&(caratteri_universali[i]==0)){
                                        rendi_universale(Grb, righe, colonne, i,  caratteri_universali, caratteri_attivi, specie_realizzate, 0);  //i: carattere da rendere universale
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


void rendi_universale(int** Grb, int righe, int colonne, int i, int* caratteri_universali, int* caratteri_attivi, int* specie_realizzate, int flag){  //i: carattere da rendere universale
        int* tspecie;
        int* tcarattere;
//cout<<righe<<colonne<<endl;
        tspecie=new int[righe];
        tcarattere=new int[colonne];

        //il carattere da rendere universale diventa attivo
        caratteri_attivi[i]=1;

        caratteri_universali[i]=1;

        // calcolo componente connessa del carattere
        for(auto j=0; j<righe; j++) tspecie[j]=0;
        for(auto j=0; j<colonne; j++) tcarattere[j]=0;

        valuta_colonna(Grb, righe, colonne, i, tspecie, tcarattere);

        for (auto j=0; j<righe; j++){ //scorro le specie per vedere a cosa connettere il carattere
                // cout<<j<<matrice[j][i]<<endl;
                if (Grb[j][i]==1){
                        // cout<<j<<endl;
                        Grb[j][i]=0; //cancello archi neri
                        // cout<<Grb[j][i]<<endl;
                }
                else if (Grb[j][i]==0) {
                        //verifica che la specie appartiene alla componente di cui fa parte il carattere. Se appartiene metti un arco rosso

                        if ((tspecie[j]==1) && (specie_realizzate[j]==0)){
                                Grb[j][i]=2;    //arco rosso tra carattere e specie della componente connessa se specie non ancora realizzata
                                // rossi[j][i]=1;
                                if(flag==1){
                                        // cout<<"estendo"<<endl;
                                        estesa[j][2*i]=1;
                                        estesa[j][2*i+1]=1;
                                }
                        }
                }

        }

/*
  cout<<"grb dentro rendi universale....."<<endl;
  for(r=0; r<righe; r++){
  for(j=0; j<colonne; j++){
  cout<<Grb[r][j];
  }
  cout<<endl;
  }
  cout<<endl;*/

/*for(r=0; r<righe; r++){
  for(j=0; j<2*colonne; j++){
  cout<<estesa[r][j];
  }
  cout<<endl;
  }
  cout<<endl;*/
//cout<<"prima di aggiornare car attivi"<<endl;
// aggiorna_caratteri_attivi(matrice, righe, colonne, caratteri_attivi, Grb, specie_realizzate);
        aggiorna_caratteri_attivi(Grb, righe, colonne, caratteri_attivi, specie_realizzate);
//  cout<<"$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$ CAR ATTIVI dopo aver reso universale "<<i<<": ";
        // for(ii=0; ii<colonne; ii++)
        // cout<<caratteri_attivi[ii];
        // cout<<endl;
        // cout<<"finito di rendere universale"<<endl;
/*cout<<",,,,,,,,,,,,,,,,,,,,,,,,grb dopo aggiornamento"<<endl;
  for(r=0; r<righe; r++){
  for(j=0; j<colonne; j++){
  cout<<Grb[r][j];
  }
  cout<<endl;
  }
  cout<<endl;*/
//cout<<"q: "<<q<<endl;
//cout<<"qui"<<endl;
        //  for(i=0; i<colonne; i++) soluzionecarattivi[q][i]=caratteri_attivi[i];
        //cout<<"qui"<<endl;
        //  cout<<"zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz"<<endl;
//q++;
//cout<<"qui"<<endl;
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
}

int valuta_riga(int** Grb, int righe, int colonne, int specie, int* tspecie, int* tcarattere){
        int j;
        //printf("inizio di valuta riga\n");
        //costruzione grafo connesso di "carattere"

        for (j=0; j<colonne; j++){
                if ((Grb[specie][j]==1) | (Grb[specie][j]==2)){
                        if (tcarattere[j]==0) {
                                tcarattere[j]=1;
                                valuta_colonna(Grb, righe, colonne, j, tspecie, tcarattere);
                        }
                }
        }


}

void aggiorna_caratteri_attivi(int** Grb, int righe, int colonne, int* caratteri_attivi, int* specie_realizzate){
        int i,j, specie,k;
        int flag;
        int* tspecie;
        int* tcarattere;

        tspecie=new int[righe];
        tcarattere=new int[colonne];
        // cout<<"aggiorno caratteri attivi"<<endl;

        //per ogni carattere attivo
        for(i=0; i<colonne; i++){
                if(caratteri_attivi[i]==1){
                        flag=0;
                        //cout<<"stabilisco se disattivare carattere "<<i<<endl;
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
                                //cout<<"disattivo carattere "<<i<<" colonna "<<colonna<<endl;
                                // cout<<"disattivo carattere "<<i<<endl;
                                caratteri_attivi[i]=0;
                                //elimino carattere e relativi archi da grafo grb
                                for(specie=0; specie<righe; specie++) Grb[specie][i]=0;
                                //cout<<"GRB dopo aver disattivato carattere:"<<endl;
                                // printMatrix(GRB,righeO,colonneO);

                                aggiorna_specie_realizzate(Grb, righe, colonne, specie_realizzate);

                                aggiorna_caratteri_attivi(Grb, righe, colonne, caratteri_attivi, specie_realizzate);
                        }
                }
        }

        // delete[] tspecie;
        //  delete[] tcarattere;
}

void aggiorna_specie_realizzate(int** Grb, int righe, int colonne, int* specie_realizzate){
        int i,j;
        int archi;

        for(i=0; i<righe; i++){ //confronto ogni specie con il vettore di caratteri attivi relativi alla stessa componente della specie.

                if(specie_realizzate[i]==0){
                        archi=0;
                        //controlla se ci sono archi entranti
                        for(j=0; j<colonne; j++){
                                if(Grb[i][j]!=0) archi=archi+1;
                        }
                        if (archi==0) {
                                // cout<<"specie "<<i<<" realizzata"<<endl;
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
                                //printf("specie connessa al carattere %d: %d", carattere, i);
                                valuta_riga(matrice, righe, colonne, i, Grb, tspecie, tcarattere);
                        }
                }
        }
}

int valuta_riga(int** matrice, int righe, int colonne, int specie, int** Grb, int* tspecie, int* tcarattere){
        int j;
        //printf("inizio di valuta riga\n");
        //costruzione grafo connesso di "carattere"

        for (j=0; j<colonne; j++){
                if ((Grb[specie][j]==1) | (Grb[specie][j]==2)){
                        if (tcarattere[j]==0) {
                                tcarattere[j]=1;
                                valuta_colonna(matrice, righe, colonne, j, Grb, tspecie, tcarattere);
                        }
                }
        }


}


bool specie_realizzata(int** matrice,int righe,int colonne,int specie, int* caratteri_universali){
        /*  cout<<"dentro specie realizzata"<<endl;
            for(i=0; i<colonne; i++) cout<<caratteri_universali[i];
            cout<<endl;
            cout<<"matrice:"<<endl;
            printMatrix(matrice, righe, colonne);*/

        for(auto i=0; i<colonne; i++){
                // cout<<i<<endl;
                if((matrice[specie][i]==1) && (caratteri_universali[i]==0)) {
                        //  cout<<"car "<<i<<"ancora da realizzare"<<endl;
                        return false;
                }
        }
        //  cout<<"realizzato tutti i caratteri"<<endl;
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


//Inverto ordine nodi percorso. es in:123-1   out: 321-1
void riordina_percorso(int* ordinato, int* percorso, int righe){
        int i, nodi;

        for(i=0; i<righe; i++) ordinato[i]=-1;
        nodi=0;
        for(i=0; i<righe; i++){
                if(percorso[i]!=-1) nodi++;
        }
        for(i=0; i<nodi; i++) ordinato[i]=percorso[nodi-1-i];
        /*  cout<<"percorso ordinato: ";
            for(i=0; i<righe; i++) cout<<ordinato[i];
            cout<<endl;*/
        //  delete[] ordinato; //ma viene eseguita questa istruzione essendo piazzata dopo il return?
}

// verifico se il carattere "carattere" appartiene alla specie "specie"
int appartiene(int carattere, int specie){
        return (matriceO[specie][carattere]==1);
}

//verifica se c  con un carattere A già nella soluzione induce le configurazioni (0,1) (1,0) (1,1) nella matrice M
int conflitto(int c){
        int i,k, flag1, flag2, flag3;

        // cout<<"verfico se "<<c<<" in conflitto"<<endl;
        for(i=0; i<colonneO; i++){
                if(inserito(i)==1){
                        // cout<<"confronto con colonna "<<i<<endl;
                        flag1=0;
                        flag2=0;
                        flag3=0;
                        for (k = 0; k < righeO; k++) {
                                if ((matriceO[k][i] == 1 ) & (matriceO[k][c] == 1)) flag1 = 1;
                                if ((matriceO[k][i] == 0) & (matriceO[k][c] == 1)) flag2 = 1;
                                if (((matriceO[k][i] == 1)) & (matriceO[k][c] == 0)) flag3 = 1;
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
        // cout<<c<<" non ancora inserito"<<endl;
        return 0;
}

//elimina eventuali righe uguali
void compattaIndottaMassimali(){
        int i,j, nr, i_matrice;
        int* copia;
        copia=new int[righe_indotta];
        for(i=0; i<righe_indotta; i++) copia[i]=-1;
        nr=0;

        /*  cout<<"matrice indotta da massimali:"<<endl;
            for(i=0; i<righe_indotta; i++){
            for(j=0; j<colonne_indotta; j++){
            cout<<matrice_indotta[i][j];
            }
            cout<<endl;
            }
            cout<<endl;*/

        //calcola le righe diverse
        copia[0]=0;
        nr++;
        for(i=1; i<righe_indotta; i++){
                // cout<<"riga "<<i<<endl;
                if(specieDiversa(i)==1){
                        // cout<<"diversa!"<<endl;
                        copia[i]=0;
                        nr++;
                }
        }
        // cout<<"numero di specie diverse: "<<nr<<endl;
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
        delete[] copia;
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
        //cout<<s1<<s2<<"sono uguali"<<endl;
        return 1;
}

int specieUguali(int* s1, int* s2, int colonne){
        int i;
        for(i=0; i<colonne; i++)
                if(s1[i]!=s2[i]) return 0;
        //cout<<s1<<s2<<"sono uguali"<<endl;
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
                //cout<<"nodo successivo: "<<percorso[i]<<endl;
        }
        /*  cout<<"PERCORSO: ";
            for(i=0; i<righe; i++) cout<<percorso[i];
            cout<<endl;*/
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
}
//prende GRB globale, ne calcola le c.c. e sulla prima componente richiama la procedura per risolvere la singola componente
void riduciMatrice(){
        int n_componenti;
        int i, j;
        int cont;
        int* universali;
        int* componentiRighe;
        cout<<"GRB in riduci matrice"<<endl;
        printMatrix(GRB, righeO, colonneO);
        // calcola le componenti connesse del grafo rosso nero

        n_componenti=calcola_componenti(GRB,righeO,colonneO);
        // cout<<"numero di componenti: "<<n_componenti+1<<endl;

        // per ogni componente GRB connessa
        //  for(contatore_componente=0; contatore_componente<=n_componenti; contatore_componente++){
        contatore_componente=0; //applico algo solo sulla prima c.c. trovata e poi se non ho finito richiamo tutto su GRB generale
        //    cout<<"componente "<<contatore_componente<<endl;


        // calcola matrice indotta dalla componente connessa di Grb
        indotta_cc(contatore_componente);
        //  matrice_con_minimali=0;  //flag per indicare se ci sono minimali nella matrice considerata
        cout<<"matrice indotta dalla c.c.:"<<endl;
        printMatrix(matrice_cc, righe_cc, colonne_cc);

        componentiRighe=new int[righeO];
        for(i=0; i<righeO;i++) componentiRighe[i]=comp_righe[i];


        universali = (int *) calloc(colonne_cc, sizeof(int));
        for (i = 0; i < colonne_cc; i++)
                universali[i] = 0;

        for(i=0; i<colonne_cc; i++){
                cont=0;
                for(j=0; j<righe_cc; j++){
                        if(matrice_cc[j][i]==2) cont++;
                }
                if(cont>0) universali[i]=1;
        }
        /*  somma_universali=0;
            for(i=0; i<colonne_cc; i++){
            somma_universali=somma_universali+universali[i];
            }
            if(somma_universali==colonne_cc){
            cout<<"Sottomatrice con soli archi rossi: la matrice non ammette soluzione";
            exit(0);
            }*/



        calcola_massimali(colonne_cc, universali, matrice_cc, righe_cc, specie_realizzate);
        // Calcolo la matrice indotta da soli massimali

        indotta_massimali(matrice_cc,righe_cc,colonne_cc,massimali);

        compattaIndottaMassimali();
        cout<<".....matrice indotta da massimali"<<endl;
        printMatrix(matriceMC, righeMC, colonneMC);
        cout<<"..............."<<endl;
        calcolaSoluzione(matriceMC, righeMC, colonneMC, componentiRighe);



        int somma=0;
        for(i=0; i<colonneO; i++) somma=somma+car_universali[i];
        if(somma==colonneO) {
                //   cout<<"Ho realizzato tutti i caratteri!"<<endl;

        }
        else{
                //  cout<<"Ricorsione!!!"<<endl;
                riduciMatrice();
        }

}
/*
  void trovaPercorsi(int** matrice, int** hasse, int righe, int colonne, int* componentiRiga){ //matrice di soli massimali
  int** percorsi;
  int singolettiSafe[righe];
  int numeroPercorso;
  int percorsoOrdinato[righe];
  int i,j,k, nSo, nSi, ii, jj;
  int g;
  //  int* c_universali;
  //  int* s_realizzate;
  //  int* c_attivi;
  //  int* soluzione_massimali;
  int cont_neri, cont_specie, cont;
  int stop;
  int flagSingoletti, somma, flagSpecie;
  cout<<"TROVA PERCORSI"<<endl;
  printMatrix(matrice,righe,colonne);
  nSo=0;
  nSi=0;


  /*     cout<<"componenti righe dentro trovaPercorsi: ";
  for(i=0; i<righeO; i++) cout<<componentiRiga[i];
  cout<<endl;*/
/******
       sorgenti=new int[righe];
       sorgenti_potenziali=new int[righe];
       sink=new int[righe];
       in_deg=new int[righe];
       specieRealizzate=new int[righe];
       for(i=0; i<righe; i++) sorgenti_potenziali[i]=1; //inizialmente suppongo che qualsiasi nodo possa essere sorgente
       for(i=0; i<righe; i++) specieRealizzate[i]=0;
//SISTEMARE CONDIZIONE ITERAZIONE: CONTROLLO SU GC MASSIMALI
//while((flag_hasse_vuoto==0)&(flag_ammissibile==1)){
// cout<<"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"<<endl;
// printMatrix(matrice,righe,colonne);
// cout<<"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"<<endl;
for(i=0; i<righe; i++){
sorgenti[i]=trova_sorgenti(i,righe);
sink[i]=trova_sink(i,righe);
in_deg[i]=inDeg(i,righe);
}
for(i=0; i<righe; i++){
if (sorgenti[i]==1){
//   cout<<i<<" sorgente"<<endl;
nSo++;
}
}

for(i=0; i<righe; i++){
if (sink[i]==1) {
//  cout<<i<<" sink"<<endl;
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

//determino se Hasse di soli singoletti
flagSingoletti=0;
somma=0;
for(i=0; i<righe; i++){
for(j=0; j<righe; j++)
somma=somma+hasse[i][j];
}
if(somma==0){
flagSingoletti=1;
cout<<"Hasse di soli singoletti!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"<<endl;
}


//determino quali percorsi sono safe
int safe[nSo*nSi];
int percorsoOrdinato[righe];
for(i=0; i<righe; i++)percorsoOrdinato[i]=-1;
for(i=0; i<nSo*nSi; i++) safe[i]=-1;
stop=0;
for(i=0; i<nSo*nSi; i++){
cout<<"Percorso numero "<<i<<endl;

if(stop==0){    //se non ho ancora trovato un percorso valido
if(percorsi[i][0]!=-1){
// for(j=0; j<righe;j++)cout<<percorsi[i][j];
// cout<<endl;
//cout<<"..................determino se percorso "<<i<<" sia safe"<<endl;
riordina_percorso(percorsoOrdinato,percorsi[i], righe); //inverto ordine dei nodi
safe[i]=realizza_percorso(matrice, righe, colonne, percorsoOrdinato);
// cout<<"safe[i].......................: "<<safe[i]<<endl;
if(safe[i]==1){
if(flagSingoletti==0){
stop=1;
k=determinaIndice(soluzione);
//   cout<<"Indice in cui copiare soluzione: "<<k<<endl;
//copio caratteri, in base alla tabella di associazione originale-indotto
copiaSoluzione(soluzione,k,percorsi[i][0], matrice, colonne);
/*   cout<<"soluzione: ";
for(c=0; c<colonneO; c++) cout<<soluzione[c]<<" ";
cout<<endl;*/
/******
 //3- realizzo i caratteri della sorgente nel GRB
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
 // realizza_specie(GRB,righeO,colonneO,percorsi[i][0],specie_realizzate, car_universali, car_attivi);
 aggiornaGRB(k,specie_realizzate, car_universali, car_attivi);
 }

 //nel caso di singoletti
 if(flagSingoletti==1){
 cout<<"percorso "<<i<<" di soli singoletti"<<endl;
 // cout<<"numero righe:"<<righe<<endl;

 //se il singoletto è uno, la specie da realizzare è quella del singoletto
 if(righe==1) {
 //  cout<<"un solo singoletto"<<endl;;
 flagSpecie=1;
 }
 //altrimenti determino quale singoletto realizzare
 else flagSpecie=specieMatrice(percorsi[i][0], matrice, colonne, componentiRiga);
 //se realizzando i caratteri del singoletto realizzo una specie della matrice iniziale
 if(flagSpecie==1){
 // cout<<"ok specie di matrice iniziale"<<endl;
 stop=1;
 k=determinaIndice(soluzione);
 copiaSoluzione(soluzione,k,percorsi[i][0], matrice, colonne);

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
 // realizza_specie(GRB,righeO,colonneO,percorsi[i][0],specie_realizzate, car_universali, car_attivi);
 aggiornaGRB(k,specie_realizzate, car_universali, car_attivi);
 }
 }
 }
 }
 }
 if((i==(nSo*nSi)-1)&(stop==0)) {
 cout<<"Non esiste un percorso safe --> no soluzione!!!"<<endl;
 exit(0);
 }
 }

 // delete[] percorsi;
 }

*/



void trovaPercorsi(int** matrice, int** hasse, int righe, int colonne, int* componentiRiga){ //matrice di soli massimali
        int** percorsi;
        int singolettiSafe[righe];
        int numeroPercorso;
        int percorsoOrdinato[righe];
        int i,j,k,c, nSo, nSi, ii, jj;
        int g,gGRB;
        //  int* c_universali;
        //  int* s_realizzate;
        //  int* c_attivi;
        //  int* soluzione_massimali;
        int cont_neri, cont_specie, cont;
        int stop;
        int flagSingoletti, somma, flagSpecie;
//cout<<"TROVA PERCORSI"<<endl;
//printMatrix(matrice,righe,colonne);
        nSo=0;
        nSi=0;


        /*     cout<<"componenti righe dentro trovaPercorsi: ";
               for(i=0; i<righeO; i++) cout<<componentiRiga[i];
               cout<<endl;*/

        sorgenti=new int[righe];
        sorgenti_potenziali=new int[righe];
        sink=new int[righe];
        in_deg=new int[righe];
        specieRealizzate=new int[righe];
        for(i=0; i<righe; i++) sorgenti_potenziali[i]=1; //inizialmente suppongo che qualsiasi nodo possa essere sorgente
        for(i=0; i<righe; i++) specieRealizzate[i]=0;
//SISTEMARE CONDIZIONE ITERAZIONE: CONTROLLO SU GC MASSIMALI
        //while((flag_hasse_vuoto==0)&(flag_ammissibile==1)){
        // cout<<"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"<<endl;
        // printMatrix(matrice,righe,colonne);
        // cout<<"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"<<endl;


        //determino se Hasse di soli singoletti
        flagSingoletti=0;
        somma=0;
        for(i=0; i<righe; i++){
                for(j=0; j<righe; j++)
                        somma=somma+hasse[i][j];
        }
        if(somma==0){
                flagSingoletti=1;
                // cout<<"Hasse di soli singoletti!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"<<endl;
        }




        //CASO DEGENERE: HASSE DI SOLI SINGOLETTI
        if(flagSingoletti==1){
                //   cout<<"HASSE DEGENERE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"<<endl;
                int percorsoGRB[righeO];
                int safeGRB[righe];


                flagSpecie=0;
                g=0;
                gGRB=0;
//determino insieme di singoletti safe
                for(i=0; i<righe; i++) singolettiSafe[i]=0;
                for(i=0; i<righe; i++)percorsoOrdinato[i]=-1;
                for(i=0; i<righe; i++){
                        percorsoOrdinato[0]=i;
                        singolettiSafe[i]=realizza_percorso(matrice, righe, colonne, percorsoOrdinato);
                        g=g+singolettiSafe[i];
                }
/*cout<<"::::::::::::::::::::::::::::::::::::::::::::::::::::singoletti safe: ";
  for (i=0; i<righe; i++) cout<<singolettiSafe[i];
  cout<<endl;*/

//determino insieme di singoletti safe nel GRB
                for(i=0; i<righe; i++) safeGRB[i]=-1;
                for(i=0; i<righeO; i++) percorsoGRB[i]=-1;
                for(i=0; i<righe; i++){
                        percorsoGRB[0]=i;
                        /* cout<<"percorsoGRB: ";
                           for(ii=0; ii<righeO; ii++) cout<<percorsoGRB[ii];
                           cout<<endl;*/
                        //safeGRB[i]=realizza_percorso(GRB, righeO, colonneO, percorsoGRB);
                        safeGRB[i]=VerificaSafeInGRB(matrice,righe,colonne,percorsoGRB[0]);
                        gGRB=gGRB+safeGRB[i];
                }
/*cout<<"numero di singoletti safe in GRB: "<<gGRB<<endl;
  cout<<"$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$singoletti safe nel GRB: ";
  for (i=0; i<righe; i++) cout<<safeGRB[i];
  cout<<endl;*/


                if(g==0){
                        cout<<"Nessun singoletto safe --> No soluzione!!!"<<endl;
                        exit(0);
                }

                if(gGRB==0){
                        cout<<"Nessun singoletto safe in GRB --> No soluzione!!!"<<endl;
                        exit(0);
                }

                stop=0;
//tra i safe, stabilisco se ce n'è uno corrispondente ad una specie della matrice iniziale. Se sì, lo scelgo
                for(i=0; i<righe; i++){
                        percorsoOrdinato[0]=i;
                        if(stop==0){    //se non ho ancora trovato un percorso valido


                                //se safe, verifico che sorgente sia safe anche in GRB
                                /*    if (singolettiSafe[i]==1) {
                                //tengo solo la sorgente del percorso, azzero il resto

                                percorsoGRB[0]=percorsoOrdinato[0];

                                cout<<"percorsoGRB: ";
                                for(ii=0; ii<righeO; ii++) cout<<percorsoGRB[ii];
                                cout<<endl;
                                safeGRB=realizza_percorso(GRB, righeO, colonneO, percorsoGRB[0]);

                                }*/

                                // cout<<"safe[i].......................: "<<singolettiSafe[i]<<endl;
                                // cout<<"safeGRB.......................: "<<safeGRB[i]<<endl;

                                if((singolettiSafe[i]==1)&(safeGRB[i]==1)){
                                        //se il singoletto è uno ed è safe, la specie da realizzare è quella del singoletto
                                        if(righe==1) {
                                                //  cout<<"un solo singoletto"<<endl;;
                                                flagSpecie=1;
                                        }
                                        //altrimenti determino quale singoletto realizzare
                                        else flagSpecie=specieMatrice(i, matrice, colonne, componentiRiga);
                                        //se realizzando i caratteri del singoletto realizzo una specie della matrice iniziale
                                        if(flagSpecie==1){
                                                // cout<<"ok specie di matrice iniziale"<<endl;
                                                stop=1;
                                                k=determinaIndice(soluzione);
                                                copiaSoluzione(soluzione,k,i, matrice, colonne);
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
                                                // realizza_specie(GRB,righeO,colonneO,percorsi[i][0],specie_realizzate, car_universali, car_attivi);
                                                aggiornaGRB(k,specie_realizzate, car_universali, car_attivi);
                                        }
                                }
                        }
                }

//se no, ne prendo uno a caso tra i safe che sia safe anche nel GRB
                if(flagSpecie==0){
                        //  cout<<"no specie di matrice iniziale --> prendo un singoletto safe a caso"<<endl;
                        for(i=0; i<righe; i++){
                                percorsoOrdinato[0]=i;
                                if(stop==0){    //se non ho ancora trovato un percorso valido

                                        /*  if (singolettiSafe[i]==1) {
                                        //tengo solo la sorgente del percorso, azzero il resto

                                        percorsoGRB[0]=percorsoOrdinato[0];

                                        cout<<"percorsoGRB: ";
                                        for(ii=0; ii<righeO; ii++) cout<<percorsoGRB[ii];
                                        cout<<endl;
                                        safeGRB=realizza_percorso(GRB, righeO, colonneO, percorsoGRB);

                                        }*/
                                        //    cout<<"safe[i].......................: "<<singolettiSafe[i]<<endl;
                                        //    cout<<"safeGRB.......................: "<<safeGRB[i]<<endl;
                                        if((singolettiSafe[i]==1)&(safeGRB[i]==1)){
                                                stop=1;
                                                k=determinaIndice(soluzione);
                                                copiaSoluzione(soluzione,k,i, matrice, colonne);
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
                                                // realizza_specie(GRB,righeO,colonneO,percorsi[i][0],specie_realizzate, car_universali, car_attivi);
                                                aggiornaGRB(k,specie_realizzate, car_universali, car_attivi);
                                        }
                                }
                        }
                }
        }

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

        else if(flagSingoletti==0){
                cout<<"HASSE NON degenere!"<<endl;
                for(i=0; i<righe; i++){
                        sorgenti[i]=trova_sorgenti(i,righe);
                        sink[i]=trova_sink(i,righe);
                        in_deg[i]=inDeg(i,righe);
                }
                for(i=0; i<righe; i++){
                        if (sorgenti[i]==1){
                                //   cout<<i<<" sorgente"<<endl;
                                nSo++;
                        }
                }

                for(i=0; i<righe; i++){
                        if (sink[i]==1) {
                                //  cout<<i<<" sink"<<endl;
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
                int safe[nSo*nSi];
                int safeGRB[nSo*nSi];
                int percorsoGRB[righeO];
                // int ii;
//        int percorsoOrdinato[righe];
                for(i=0; i<righe; i++)percorsoOrdinato[i]=-1;
                for(i=0; i<nSo*nSi; i++) safe[i]=-1;
                for(i=0; i<nSo*nSi; i++) safeGRB[i]=-1;
                for(i=0; i<righeO; i++) percorsoGRB[i]=-1;
                stop=0;
                for(i=0; i<nSo*nSi; i++){
                        //   cout<<"Percorso numero "<<i<<endl;

                        if(stop==0){    //se non ho ancora trovato un percorso valido
                                if(percorsi[i][0]!=-1){
                                        // for(j=0; j<righe;j++)cout<<percorsi[i][j];
                                        // cout<<endl;
                                        //cout<<"..................determino se percorso "<<i<<" sia safe"<<endl;
                                        riordina_percorso(percorsoOrdinato,percorsi[i], righe); //inverto ordine dei nodi
                                        // cout<<"percorso ordinato: ";
                                        // for(ii=0; ii<righe; ii++) cout<<percorsoOrdinato[ii];
                                        // cout<<endl;
                                        safe[i]=realizza_percorso(matrice, righe, colonne, percorsoOrdinato);
                                        cout<<"safe[i].......................: "<<safe[i]<<endl;
                                        //se safe, verifico che sorgente sia safe anche in GRB
                                        if(safe[i]==1){
                                                //tengo solo la sorgente del percorso, azzero il resto
                                                int p;
                                                int pSorgente;
                                                if(percorsoOrdinato[righe-1]!=-1){
                                                        percorsoGRB[0]=percorsoOrdinato[righe-1];
                                                }
                                                else {
                                                        for(p=0; p<righe-1; p++){
                                                                if((percorsoOrdinato[p]!=-1)&(percorsoOrdinato[p+1]==-1)) pSorgente=p;
                                                        }
                                                        cout<<"posizioneSorgente: "<<pSorgente<<endl;
                                                        percorsoGRB[0]=percorsoOrdinato[pSorgente];
                                                }
                                                cout<<"percorsoGRB: ";
                                                for(ii=0; ii<righeO; ii++) cout<<percorsoGRB[ii];
                                                cout<<endl;
                                                // safeGRB[i]=realizza_percorso(matriceO,righeO,colonneO,percorsoGRB);
                                                safeGRB[i]=VerificaSafeInGRB(matrice,righe,colonne,percorsoGRB[0]);

                                        }
                                        cout<<"safe[i].......................: "<<safe[i]<<endl;
                                        cout<<"safeGRB[i].......................: "<<safeGRB[i]<<endl;
                                        if((safe[i]==1)&(safeGRB[i]==1)){
                                                stop=1;
                                                k=determinaIndice(soluzione);
                                                //   cout<<"Indice in cui copiare soluzione: "<<k<<endl;
                                                //copio caratteri, in base alla tabella di associazione originale-indotto
                                                copiaSoluzione(soluzione,k,percorsi[i][0], matrice, colonne);
                                                /*   cout<<"soluzione: ";
                                                     for(c=0; c<colonneO; c++) cout<<soluzione[c]<<" ";
                                                     cout<<endl;*/

                                                //3- realizzo i caratteri della sorgente nel GRB
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
                                                // realizza_specie(GRB,righeO,colonneO,percorsi[i][0],specie_realizzate, car_universali, car_attivi);
                                                aggiornaGRB(k,specie_realizzate, car_universali, car_attivi);

                                        }
                                }
                        }
                        if((i==(nSo*nSi)-1)&(stop==0)) {
                                cout<<"No soluzione!!!"<<endl;
                                exit(0);
                        }
                }
        }

        // delete[] percorsi;
}



int specieMatrice(int specie, int** matrice, int colonne, int* componentiRiga){
        int i,j,trovata,cont;
        int* car_attivi;
        int* car_singoletto;
        int* verifica;
/*cout<<"dentro specieMatrice________________________________________________________________"<<endl;

  cout<<"componenti righe dentro specieMatrice: ";
  for(i=0; i<righeO; i++) cout<<componentiRiga[i];
  cout<<endl;
  trovata=0;*/

        verifica=new int[colonneO];
        for(i=0; i<colonneO; i++) verifica[i]=0;

        //A: determino caratteri attivi del GRB
        car_attivi=new int[colonneO];
        for(i=0; i<colonneO; i++){
                cont=0;
                for(j=0; j<righeO; j++){
                        if(GRB[j][i]==2) cont++;
                }
                if(cont==0) car_attivi[i]=0;
                if(cont>0) car_attivi[i]=1;
        }
        //se un carattere è stato attivato ed è universale nella componente che considero, è attivo
        for(i=0; i<colonneO; i++){
                if(universale(i, componentiRiga)) car_attivi[i]=1;
        }
        /*   cout<<"caratteri attivi:";
             for(i=0; i<colonneO; i++) cout<<car_attivi[i];
             cout<<endl;*/

        //B: determino insieme dei caratteri da attivare considerando il singoletto in questione
        car_singoletto=new int[colonneO];
        for(i=0; i<colonneO;i++) car_singoletto[i]=0;
        for(i=0; i<colonne;i++){
                if(matrice[specie][i]==1){
                        // cout<<"carattere da attivare "<<corrispondenzaMC[i]<<endl;
                        car_singoletto[corrispondenzaMC[i]]=1;
                }
        }
        //   cout<<"caratteri singoletto:";
        // for(i=0; i<colonneO; i++) cout<<car_singoletto[i];
        // cout<<endl;

        trovata=0;
        //verifico se caratteri A + car B = specie della matrice iniziale
        /*   for(i=0; i<righeO; i++){
             ko=0;
             if(trovata==0){
             for(j=0; j<colonneO; j++){
             if(matriceO[i][j]==1){
             if((car_attivi[j]==0)&(car_singoletto[j]==0)) ko++;
             }
             }
             if(ko==0) trovata=1;
             }
             }*/

        //costruisco specie da verificare: A+B
        for(i=0; i<colonneO; i++){
                if(car_attivi[i]==1) verifica[i]=1;
                if(car_singoletto[i]==1) verifica[i]=1;
        }
        //verifico se la specie costruita corrisponde ad una specie della matrice iniziale
        for(i=0; i<righeO; i++){
                trovata=specieUguali(verifica, matriceO[i], colonneO);
                if(trovata==1) {
                        //   cout<<"trovata specie corrispondente!!"<<endl;
                        return 1;
                }
        }


        delete[] car_attivi;
        delete[] car_singoletto;
        delete[] verifica;
        //  cout<<"no specie corrispondente"<<endl;
        return 0;
}

//verifico se un carattere è universale nella componente considerata
int universale(int carattere, int* componentiRiga){
        int i;
        /*   cout<<"verifico se "<<carattere<<" universale"<<endl;
             cout<<"componenti righe dentro universale: ";
             for(i=0; i<righeO; i++) cout<<componentiRiga[i];
             cout<<endl;*/
        for(i=0; i<righeO; i++){
                //se la riga fa parte della componente connessa
                if(componentiRiga[i]==0){
                        //   cout<<"riga "<<i<<endl;
                        if(matriceO[i][carattere]==0){
                                //   cout<<"non universale"<<endl;
                                return 0;
                        }
                }
        }
        //   cout<<"universale!"<<endl;
        return 1;
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
        // cout<<"Specie nella matrice di soli massimali: "<<specie<<endl;
        for(i=0; i<colonne; i++){
                //      cout<<"Indice in cui copiare:"<<indice<<endl;
                if(matrice[specie][i]==1) {
                        soluzione[indice]=corrispondenzaMC[i];
                        indice++;
                }
        }
}

void aggiornaGRB(int k,int* specie_realizzate,int* car_universali, int* car_attivi){
        //per ogni carattere della specie non ancora universale, rend universale
        for(auto i=k; i<colonneO; i++){
                if(soluzione[i]!=-1){
                        cout<<"____________________________________________________________REALIZZO IL CARATTERE "<<soluzione[i]<<endl;
                        //  cout<<"GRB prima"<<endl;
                        //  printMatrix(Grb,righeO, colonneO);
                        rendi_universale(GRB, righeO, colonneO, soluzione[i], car_universali, car_attivi, specie_realizzate, 1);  //i: carattere da rendere universale
                        //rendi_universale(GRB, righeO, colonneO, soluzione[i], car_universali, car_attivi, specie_realizzate, 1);  //i: carattere da rendere universale
                        // cout<<"GRB dopo"<<endl;
                        //  printMatrix(GRB,righeO, colonneO);
                        //  estendi(soluzione[i], Grb);

                }
        }
}

// verifica se tra le due colonne esiste la sottomatrice proibita
// restituisce 0 se esiste la sottomatrice proibita, 1 se non esiste

int sottomatriceProibita(int ** a, int c1, int c2) {

        int i;

        int flag1, flag2, flag3;
        flag1 = flag2 = flag3 = 0;

        //printf("\nPRIMA DEL FOR Flag 1: %d \t flag2: %d \t flag3: %d\n", flag1, flag2, flag3);

        for (i = 0; i < righeO; i++) {
                //flag1 = flag2 = flag3 = 0;
                if ((a[i][c1] == 0 ) & (a[i][c2] == 1)) {
                        flag1 = 1;
                        //printf("\n C'e' 0 1 tra la colonna %d e la colonna %d alla riga %d\n", c1, c2, i);
                }
                if ((a[i][c1] == 1 ) & (a[i][c2] == 0)) {
                        flag2 = 1;
                        //printf("\n C'e' 1 0 tra la colonna %d e la colonna %d alla riga %d\n", c1, c2, i);
                }
                if ((a[i][c1] == 1 ) & (a[i][c2] == 1)) {
                        flag3 = 1;
                        //printf("\n C'e' 1 1 tra la colonna %d e la colonna %d alla riga %d\n", c1, c2, i);
                }
        }
        //printf("\nFlag 1: %d \t flag2: %d \t flag3: %d\n", flag1, flag2, flag3);
        if (flag1 & flag2 & flag3) return 1; //esiste sottomatrice proibita
        else
                return 0;  //non esiste sottomatrice proibita
}

int VerificaSafeInGRB(int** matrice, int righe, int colonne, int specie){
        int i,j, cont_neri, cont_specie, cont;
        int** grb;
        int* c_universali;
        int* s_realizzate;
        int* c_attivi;

        grb = (int **)calloc(righeO, sizeof(int *));
        for (i = 0; i < righeO; i++){
                grb[i] = (int *)calloc(colonneO, sizeof(int));
        }

        for (i = 0; i < righeO; i++) {
                for (j = 0; j < colonneO; j++) {
                        //  grb[i][j]=GRB[i][j];
                        grb[i][j]=GRB[i][j];

                }
        }

        c_universali=new int[colonneO];
        for(i=0; i<colonneO; i++){
                cont_neri=0;
                for(j=0; j<righeO; j++){
                        if(grb[j][i]==1) {
                                cont_neri++;
                        }
                }
                if(cont_neri>0) c_universali[i]=0;
                if(cont_neri==0) c_universali[i]=1;
        }
        //specie realizzate: nessun arco entrante.
        s_realizzate=new int[righeO];
        for(i=0; i<righeO; i++){
                cont_specie=0;
                for(j=0; j<colonneO; j++){
                        if(grb[i][j]!=0) {
                                cont_specie++;
                        }
                }
                if(cont_specie!=0) s_realizzate[i]=0;
                if(cont_specie==0) s_realizzate[i]=1;
        }

        //caratteri attivi: attivo se reso universale e NON connesso con archi rossi a tutte le specie della sua componente
        c_attivi=new int[colonneO];
        for(i=0; i<colonneO; i++) c_attivi[i]=0;
        for(i=0; i<colonneO; i++){
                if (c_universali[i]==1){
                        cont=0;
                        for(j=0; j<righeO; j++){
                                if(grb[j][i]==2) cont++;
                        }
                        if(cont==righeO) c_attivi[i]=0;
                        if(cont<righeO) c_attivi[i]=1;
                }
        }
        for(i=0; i<righe; i++){
                if(matrice[specie][i]==1) {
                        cout<<"provo a rendere universale "<<corrispondenzaMC[i]<<" in GRB"<<endl;
                        rendi_universale(grb, righeO, colonneO, corrispondenzaMC[i], c_universali, c_attivi, s_realizzate, 0);
                }
        }

        printMatrix(grb,righeO, colonneO);
        if(sigmaRossi(grb,righeO,colonneO)) return 0;
        return 1;
}

int sigmaRossi(int** matrice, int righe, int colonne){
        int i,j;
        int c1, c2;
        int flag20, flag02, flag22;

        for(c1=0; c1<colonne-1; c1++){
                for(c2=1; c2<colonne; c2++){
                        if(c1!=c2){
                                flag20=0;
                                flag02=0;
                                flag22=0;

                                for (i = 0; i < righe; i++) {
                                        if ((matrice[i][c1] == 0 ) & (matrice[i][c2] == 2)) flag02 = 1;
                                        if ((matrice[i][c1] == 2 ) & (matrice[i][c2] == 0)) flag20 = 1;
                                        if ((matrice[i][c1] == 2 ) & (matrice[i][c2] == 2)) flag22 = 1;
                                }
                                if (flag02 & flag20 & flag22) return 1; //sigma nero
                        }
                }
        }
        return 0;

}
