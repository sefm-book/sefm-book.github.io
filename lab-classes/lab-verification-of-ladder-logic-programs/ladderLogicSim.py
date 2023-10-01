# This work is licensed under a Creative Commons
# Attribution-ShareAlike 4.0 International License.
# http://creativecommons.org/licenses/by-sa/4.0/

# Authors: Liam O'Reilly and Markus Roggenbach

import random

# This program simulates a ladder logic program implementing a pedestrian crossing.
# It is structure in such a way that it can be adapted by changing four functions.
# We store state as a dictionary of variable names to boolean values.


# Produce the pre-initial state of the system.
# This function returns a state (i.e., dictionary) of all variables and their initial boolean values.
# Internal state variables are false, while input are random booleans.
def pre_initial_state():
    random_button_state = random.randint(0, 1) == 0
    # All variables in the state are false, except button which is randomly true/false.
    # This gives us one of two possible initial states.
    return {"button": random_button_state, "request": False, "old_sh": False, "old_sl": False, "sh": False, "sl": False,
            "pg": False, "pgf": False, "pr": False, "tg": False, "ta": False, "tr": False, "taf": False}


# Read input of the system.
# This function accepts the current state and provides an updated (copied) version with the newly read input.
def read_input(state):
    new_state = state.copy()

    valid_value_read = False
    input_val = None
    while not valid_value_read:
        input_val = input("Is the button pushed (enter 0 for No, 1 for Yes, q to quit)? ").lower()
        if input_val in ['0', '1', 'q']:
            valid_value_read = True
        else:
            print("Invalid input. Please try again.")
            print()

    if input_val == 'q':
        exit()

    # Update the state with the new boolean input value.
    new_state['button'] = input_val == '1'

    return new_state


# Compute the next state from the current state.
# This function accepts the current state and provides an updated (copied) version.
def compute_next_state(s):
    # We use s to mean current_state and ns to mean new_state to make things a little more readable.
    ns = s.copy()

    ns['old_sh'] = s['sh']
    ns['old_sl'] = s['sl']

    ns['sh'] = (ns['old_sh'] and not ns['old_sl']) or (not ns['old_sh'] and ns['old_sl'])
    ns['sl'] = (ns['old_sh'] and not ns['old_sl']) or (
        not s['request'] and s['button'] and not ns['old_sl'])

    ns['request'] = (s['button'] and not ns['old_sh']) or (s['button'] and not ns['old_sl']) or (
        s['request'] and not s['button'] and not ns['old_sh']) or (
            s['request'] and not s['button'] and not ns['old_sl'])

    ns['pg'] = ns['old_sh'] and not ns['old_sl']
    ns['pgf'] = ns['old_sh'] and ns['old_sl']
    ns['pr'] = not ns['old_sh']
    ns['tg'] = (not ns['old_sh'] and not ns['old_sl']) or (not s['button'] and not s['request'])
    ns['ta'] = not ns['old_sh'] and ns['old_sl']
    ns['tr'] = ns['old_sh'] and not ns['old_sl']
    ns['taf'] = ns['old_sh'] and ns['old_sl']

    return ns


# Print the output from the current state.
# This function accepts the current state and should simply print the variables a user can inspect.
def print_output(state):
    print("Internal State")
    util_print_list(state, ["sh", "sl", "request", "button"])
    print("Lights")
    output_only_true_in_row(state, ["tg", "ta", "tr", "taf"], "vehicle")
    output_only_true_in_row(state, ["pg", "pgf", "pr"], "pedestrian")


####################################################
# There is no need to edit anything below this line.
####################################################


# Print a list of variables and their values from the current state.
def util_print_list(state, variable_names_to_show):
    for variable_name in variable_names_to_show:
        value = state[variable_name]
        value_as_digit = "1" if value else "0"
        print(f"\t {variable_name:<10}: {value_as_digit}")


# Print all variables from a given list which are true.
# A label is also printed to say what the variables represent.
def output_only_true_in_row(state, variable_names_to_show, label):
    true_variable_names_to_show = []

    for variable_name in variable_names_to_show:
        value = state[variable_name]
        if value:
            true_variable_names_to_show.append(variable_name)

    variable_output = ", ".join(true_variable_names_to_show)
    print(f"\t {label:<10}: {variable_output}")


# Main function implementing the main loop of the ladder logic simulator.
def main():
    cycle = 1
    # Create the initial state by passing the pre-initial state through the
    # cycle once to produce the initial state.
    state = pre_initial_state()
    state = compute_next_state(state)

    print("Initial State")
    print("-------------")
    print_output(state)

    while True:
        print()
        print("\nCycle: %d" % cycle)
        print("-----------")

        state = read_input(state)
        state = compute_next_state(state)
        cycle += 1

        print()
        print("Initial State")
        print("-------------")
        print_output(state)


# Invoke the main function
if __name__ == "__main__":
    main()
    