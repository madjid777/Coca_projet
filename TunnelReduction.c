#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"

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

// ***** Sous-formules de la réduction ***** //

static Z3_ast formula_initial_and_final_positions(Z3_context ctx,
                                                  const TunnelNetwork network,
                                                  int length)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(length);

    // Il faudra récupérer les indices de s et d dans le graphe :
    int s = tn_get_source(network);      // à adapter selon TunnelNetwork.h
    int d = tn_get_destination(network); // idem

    // On va stocker plusieurs petites contraintes puis tout AND
    Z3_ast constraints[20]; // largement suffisant ici
    int k = 0;

    // -----------------------
    // 1) Position 0 : node = s, height = 0
    // -----------------------

    // On impose : x_(s, 0, 0) = true
    constraints[k++] = tn_path_variable(ctx, s, 0, 0);

    // Pour tous les autres (node, height) à pos=0 :
    // x_(node,0,height) = false, sauf (s,0,0)
    for (int node = 0; node < num_nodes; node++)
    {
        for (int h = 0; h < stack_size; h++)
        {
            if (node == s && h == 0)
                continue;
            Z3_ast var = tn_path_variable(ctx, node, 0, h);
            Z3_ast not_var = Z3_mk_not(ctx, var);
            constraints[k++] = not_var;
        }
    }

    // Pile à pos = 0 : [4] et rien au-dessus
    // y_(0,0,4) = true ; y_(0,0,6) = false
    constraints[k++] = tn_4_variable(ctx, 0, 0);
    constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, 0));

    // Pour h >= 1, ni 4 ni 6
    for (int h = 1; h < stack_size; h++)
    {
        constraints[k++] = Z3_mk_not(ctx, tn_4_variable(ctx, 0, h));
        constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, h));
    }

    // -----------------------
    // 2) Position length : node = d, height = 0
    // -----------------------

    // x_(d, length, 0) = true
    constraints[k++] = tn_path_variable(ctx, d, length, 0);

    // Tous les autres x_(node,length,h) = false
    for (int node = 0; node < num_nodes; node++)
    {
        for (int h = 0; h < stack_size; h++)
        {
            if (node == d && h == 0)
                continue;
            Z3_ast var = tn_path_variable(ctx, node, length, h);
            Z3_ast not_var = Z3_mk_not(ctx, var);
            constraints[k++] = not_var;
        }
    }

    // Pile à pos = length : encore [4], hauteur 0
    constraints[k++] = tn_4_variable(ctx, length, 0);
    constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, length, 0));

    for (int h = 1; h < stack_size; h++)
    {
        constraints[k++] = Z3_mk_not(ctx, tn_4_variable(ctx, length, h));
        constraints[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, length, h));
    }

    // On renvoie la conjonction de toutes ces contraintes
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