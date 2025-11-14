#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"
#include "TunnelNetwork.h"

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,4}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,6}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Wrapper to have the correct size of the array representing the stack (correct cells of the stack will be from 0 to (get_stack_size(length)-1)).
 *
 * @param length The length of the sought path.
 * @return int
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}

/**
 * formula_initial_and_final_positions : Formule SAT pour les contraintes de positions initiale et finale
 *
 * Cette fonction génère une formule booléenne qui encode les contraintes suivantes :
 * 1. À la position 0 : le chemin commence au nœud source 's' avec une pile contenant uniquement [4]
 * 2. À la position 'length' : le chemin termine au nœud destination 'd' avec une pile revenue à [4]
 *
 * Représentation visuelle :
 * Position 0 (départ)          Position length (arrivée)
 * ┌─────────────┐              ┌─────────────┐
 * │ Nœud: s     │              │ Nœud: d     │
 * │ Hauteur: 0  │  ──────────> │ Hauteur: 0  │
 * │ Pile: [4]   │              │ Pile: [4]   │
 * └─────────────┘              └─────────────┘
 *
 * param ctx = Le contexte du solveur Z3 (utilisé pour créer les variables et formules)
 * param network = Le réseau de tunnels contenant les nœuds et leurs connexions
 * param length = La longueur du chemin recherché (nombre de transitions entre nœuds)
 * return = Une formule Z3 (conjonction de toutes les contraintes) qui sera satisfaite si et seulement si
 *         les conditions initiales et finales sont respectées
 */

static Z3_ast formula_initial_and_final_positions(Z3_context ctx,
                                                  const TunnelNetwork network,
                                                  int length)
{
    // ===== RÉCUPÉRATION DES PARAMÈTRES DU RÉSEAU =====

    // Nombre total de nœuds dans le graphe (récupéré depuis TunnelNetwork.h)
    int num_nodes = tn_get_num_nodes(network);

    // Taille maximale de la pile : length/2 + 1 cellules
    // Exemple : pour un chemin de longueur 10, on a besoin d'au plus 6 cellules de pile
    int stack_size = get_stack_size(length);

    // Identifiant du nœud source (point de départ du chemin)
    int s = tn_get_initial(network);

    // Identifiant du nœud destination (point d'arrivée du chemin)
    int d = tn_get_final(network);

    // ===== INITIALISATION DU TABLEAU DE CONTRAINTES =====

    // Tableau qui va contenir 20 cases pour stocker des contraintes booléennes (T or F).
    // Dimensionné large pour accueillir toutes les contraintes nécessaires
    Z3_ast constraints[20];

    // Compteur k pour suivre le nombre de contraintes ajoutées dans le tableau
    int k = 0;

    // ========================================================================
    // PARTIE 1 : CONTRAINTES À LA POSITION INITIALE (pos = 0)
    // ========================================================================

    // -----------------------
    // 1.A) Configuration du nœud initial
    // -----------------------

    // CONTRAINTE : Le chemin démarre exactement au nœud source 's' avec hauteur de pile 0
    // Variable booléenne : x_{s,0,0} = true
    // Signification : À la position 0, on est au nœud s, avec la pile contenant 1 seul élément (hauteur = 0)
    constraints[k++] = tn_path_variable(ctx, s, 0, 0);

    // CONTRAINTE : Aucune autre configuration (nœud, hauteur) n'est possible à la position 0
    // Pour tous les couples (node, h) différents de (s, 0) : x_{node,0,h} = false
    for (int node = 0; node < num_nodes; node++)
    {
        for (int h = 0; h < stack_size; h++)
        {
            // On saute la configuration (s, 0) qui est déjà fixée à true
            if (node == s && h == 0)
                continue;

            // Création de la variable x_{node,0,h}
            Z3_ast var = tn_path_variable(ctx, node, 0, h);

            // Ajout de la contrainte : NOT(x_{node,0,h})
            // Cela interdit d'être à ce nœud ou à cette hauteur de pile
            Z3_ast not_var = Z3_mk_not(ctx, var);
            constraints[k++] = not_var;
        }
    }

    // -----------------------
    // 1.B) État initial de la pile : [4]
    // -----------------------

    // CONTRAINTE : À la position 0, la cellule de base (hauteur 0) contient la valeur 4
    // Variable : y_{0,0,4} = true
    // Signification : La pile commence avec un unique élément de valeur 4
    constraints[k++] = tn_4_variable(ctx, 0, 0);

    // CONTRAINTE : Cette même cellule ne contient PAS la valeur 6
    // Variable : y_{0,0,6} = false
    // Cela garantit qu'une cellule contient soit 4, soit 6, mais pas les deux
    constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, 0));

    // CONTRAINTE : Toutes les cellules au-dessus de la hauteur 0 sont vides
    // Pour h = 1, 2, ..., stack_size-1 : y_{0,h,4} = false ET y_{0,h,6} = false
    // Cela signifie que la pile ne contient qu'un seul élément au départ
    for (int h = 1; h < stack_size; h++)
    {
        // La cellule h ne contient pas de 4
        constraints[k++] = Z3_mk_not(ctx, tn_4_variable(ctx, 0, h));

        // La cellule h ne contient pas de 6
        constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, h));
    }

    // ========================================================================
    // PARTIE 2 : CONTRAINTES À LA POSITION FINALE (pos = length)
    // ========================================================================

    // -----------------------
    // 2.A) Configuration du nœud final
    // -----------------------

    // CONTRAINTE : Le chemin se termine exactement au nœud destination 'd' avec hauteur de pile 0
    // Variable : x_{d,length,0} = true
    // Signification : À la position finale, on doit être au nœud d avec la pile revenue à 1 élément
    constraints[k++] = tn_path_variable(ctx, d, length, 0);

    // CONTRAINTE : Aucune autre configuration (nœud, hauteur) n'est possible à la position finale
    // Pour tous les couples (node, h) différents de (d, 0) : x_{node,length,h} = false
    for (int node = 0; node < num_nodes; node++)
    {
        for (int h = 0; h < stack_size; h++)
        {
            // On saute la configuration (d, 0) qui est déjà fixée à true
            if (node == d && h == 0)
                continue;

            // Création de la variable x_{node,length,h}
            Z3_ast var = tn_path_variable(ctx, node, length, h);

            // Ajout de la contrainte : NOT(x_{node,length,h})
            // On ne peut être à aucun autre nœud ni avoir une autre hauteur de pile
            Z3_ast not_var = Z3_mk_not(ctx, var);
            constraints[k++] = not_var;
        }
    }

    // -----------------------
    // 2.B) État final de la pile : [4] (identique à l'état initial)
    // -----------------------

    // CONTRAINTE : À la position finale, la cellule de base contient la valeur 4
    // Variable : y_{length,0,4} = true
    // La pile doit être revenue exactement à son état initial
    constraints[k++] = tn_4_variable(ctx, length, 0);

    // CONTRAINTE : Cette cellule ne contient PAS la valeur 6
    // Variable : y_{length,0,6} = false
    constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, length, 0));

    // CONTRAINTE : Toutes les cellules au-dessus sont vides (comme au départ)
    // Pour h = 1, 2, ..., stack_size-1 : y_{length,h,4} = false ET y_{length,h,6} = false
    for (int h = 1; h < stack_size; h++)
    {
        // La cellule h ne contient pas de 4
        constraints[k++] = Z3_mk_not(ctx, tn_4_variable(ctx, length, h));

        // La cellule h ne contient pas de 6
        constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, length, h));
    }

    // ===== RETOUR DE LA FORMULE FINALE =====

    // Retourne la conjonction (AND logique) de toutes les contraintes accumulées
    // La formule est satisfaite si et seulement si TOUTES les contraintes sont vraies simultanément
    // Cela garantit que le chemin commence correctement en 's' et termine en 'd' avec la pile [4]
    return Z3_mk_and(ctx, k, constraints);
}

// Unicité : à chaque position, exactement un (node,height)
static Z3_ast formula_unique_node_per_position(Z3_context ctx,
                                               const TunnelNetwork network,
                                               int length);

// Chemin simple : chaque node apparaît au plus une fois
static Z3_ast formula_simple_path(Z3_context ctx,
                                  const TunnelNetwork network,
                                  int length);

// Transitions valides : graphe + pile (T, PUSH, POP)
static Z3_ast formula_valid_transitions(Z3_context ctx,
                                        const TunnelNetwork network,
                                        int length);

// Fonction qui permet de construire la reduction

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    Z3_ast parts[4];
    int k = 0;

    parts[k++] = formula_initial_and_final_positions(ctx, network, length);
    parts[k++] = formula_unique_node_per_position(ctx, network, length);
    parts[k++] = formula_simple_path(ctx, network, length);
    parts[k++] = formula_valid_transitions(ctx, network, length);

    return Z3_mk_and(ctx, k, parts);
}

// Lisent le chemin dans le modèle

void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1;
        int src_height = -1;
        int tgt = -1;
        int tgt_height = -1;
        for (int n = 0; n < num_nodes; n++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos, height)))
                {
                    src = n;
                    src_height = height;
                }
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos + 1, height)))
                {
                    tgt = n;
                    tgt_height = height;
                }
            }
        }
        int action = 0;
        if (src_height == tgt_height)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                action = transmit_4;
            else
                action = transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = push_4_4;
                else
                    action = push_4_6;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = push_6_4;
            else
                action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                {
                    if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                        action = pop_4_4;
                    else
                        action = pop_6_4;
                }
                else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = pop_4_6;
                else
                    action = pop_6_6;
            }
        }
        path[pos] = tn_step_create(action, src, tgt);
    }
}

// Fonction qui affiche le modèle

void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound + 1; pos++)
    {
        printf("At pos %d:\nState: ", pos);
        int num_seen = 0;
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, node, pos, height)))
                {
                    printf("(%s,%d) ", tn_get_node_name(network, node), height);
                    num_seen++;
                }
            }
        }
        if (num_seen == 0)
            printf("No node at that position !\n");
        else
            printf("\n");
        if (num_seen > 1)
            printf("Several pair node,height!\n");
        printf("Stack: ");
        bool misdefined = false;
        bool above_top = false;
        for (int height = 0; height < stack_size; height++)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, height)))
            {
                if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
                {
                    printf("|X");
                    misdefined = true;
                }
                else
                {
                    printf("|4");
                    if (above_top)
                        misdefined = true;
                }
            }
            else if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
            {
                printf("|6");
                if (above_top)
                    misdefined = true;
            }
            else
            {
                printf("| ");
                above_top = true;
            }
        }
        printf("\n");
        if (misdefined)
            printf("Warning: ill-defined stack\n");
    }
    return;
}
