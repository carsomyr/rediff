#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright (c) 2011 Roy Liu
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#   * Redistributions of source code must retain the above copyright notice,
#     this list of conditions and the following disclaimer.
#   * Redistributions in binary form must reproduce the above copyright notice,
#     this list of conditions and the following disclaimer in the documentation
#     and/or other materials provided with the distribution.
#   * Neither the name of the author nor the names of any contributors may be
#     used to endorse or promote products derived from this software without
#     specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""A script for filtering unified diff output and recolorizing it with intraline changes highlighted.
"""

__author__ = "Roy Liu <carsomyr@gmail.com>"

import bisect
import re
import sys
from abc import ABCMeta
from abc import abstractmethod
from argparse import ArgumentParser
from itertools import chain

#----------------------------------------------------------------------------------------------------------------------#
# Opcode post-processing filters.                                                                                      #
#----------------------------------------------------------------------------------------------------------------------#

class OpcodeFilter(object):
    """An abstract base class for implementing edit script opcode post-processing filters.
    """

    __metaclass__ = ABCMeta

    def __init__(self):
        """Default constructor.
        """

    @abstractmethod
    def __call__(self, opcodes, s1, s2):
        """Post-processes the given edit script opcodes arising from the difference of two strings.

        Args:
            opcodes: The opcodes.
            s1: The first string.
            s2: The second string.

        Returns:
            The post-processed opcodes.
        """

class IdentityFilter(OpcodeFilter):
    """An implementation of OpcodeFilter that simply returns its input.
    """

    def __init__(self):
        """Default constructor.
        """
        super(IdentityFilter, self).__init__()

    def __call__(self, opcodes, s1, s2):
        return opcodes

class ChainFilter(OpcodeFilter):
    """An implementation of OpcodeFilter for chaining filters and applying them in order, with each filter's output
    being used as its successor's input.
    """

    def __init__(self, *filters):
        """Default constructor.

        Args:
            filters: The filters to chain, declared in order of application.
        """
        super(ChainFilter, self).__init__()

        self.filters = list(filters)

    def __call__(self, opcodes, s1, s2):

        for f in self.filters:
            opcodes = f(opcodes, s1, s2)

        return opcodes

class MergeFilter(OpcodeFilter):
    """An implementation of OpcodeFilter for merging consecutive opcodes that have equal tags.
    """

    def __init__(self):
        """Default constructor.
        """
        super(MergeFilter, self).__init__()

    def __call__(self, opcodes, s1, s2):

        i_curr = i_next = 1
        n_opcodes = len(opcodes)

        while i_next < n_opcodes:
            opcodes[i_curr] = opcodes[i_next]
            i_curr = MergeFilter.merge(opcodes, i_curr)
            i_curr += 1
            i_next += 1

        return opcodes[:i_curr]

    @staticmethod
    def merge(opcodes, index):
        """Attempts to merge the opcodes at index and (index - 1).

        Args:
            opcodes: The opcodes.
            index: The working index.

        Returns:
            The updated working index.
        """

        (tag1, start_left1, end_left1, start_left2, end_left2) = opcodes[index - 1]
        (tag2, start_right1, end_right1, start_right2, end_right2) = opcodes[index]

        assert end_left1 == start_right1 and end_left2 == start_right2, \
            "The opcode boundary invariant does not hold."

        if tag1 == tag2:
            opcodes[index - 1] = (tag1, start_left1, end_right1, start_left2, end_right2)
            index -= 1
        elif ((tag1 == "delete" and tag2 == "replace")
              or (tag1 == "replace" and tag2 == "delete")
              or (tag1 == "insert" and tag2 == "replace")
              or (tag1 == "replace" and tag2 == "insert")
              or (tag1 == "delete" and tag2 == "insert")
              or (tag1 == "insert" and tag2 == "delete")):
            opcodes[index - 1] = ("replace", start_left1, end_right1, start_left2, end_right2)
            index -= 1

        return index

class ShiftFilter(MergeFilter):
    """An implementation of OpcodeFilter for aligning difference regions with semantically coherent locations, as
    described by http://neil.fraser.name/writing/diff/ in Section 3.2.2. More specifically, alignments are scored based
    on what they're adjacent to, e.g., three points for line breaks and two points for other whitespace. Changes are
    then propagated accordingly in acceptance of the highest scoring, leftmost alignment.
    """

    whitespace_pattern = re.compile(b"^\\s$")

    not_alphanumeric_pattern = re.compile(b"^\\W$")

    def __init__(self):
        """Default constructor.
        """
        super(ShiftFilter, self).__init__()

    def __call__(self, opcodes, s1, s2):

        i_curr = i_next = 2
        n_opcodes = len(opcodes)

        while i_next < n_opcodes:
            opcodes[i_curr] = opcodes[i_next]
            (i_curr, i_next) = ShiftFilter.shift(opcodes, s1, s2, i_curr, i_next)
            i_curr += 1
            i_next += 1

        return opcodes[:i_curr]

    @staticmethod
    def shift(opcodes, s1, s2, index, next_index):
        """Attempts to shift the opcode at (index - 1) against the opcodes at (index - 2) and index.

        Args:
            opcodes: The opcodes.
            s1: The first string.
            s2: The second string.
            index: The working index.
            next_index: The next index.

        Returns:
            A 2-tuple containing the updated working and next indices.
        """

        (tag_left, start_left1, end_left1, start_left2, end_left2) = opcodes[index - 2]
        (tag_middle, start_middle1, end_middle1, start_middle2, end_middle2) = opcodes[index - 1]
        (tag_right, start_right1, end_right1, start_right2, end_right2) = opcodes[index]

        assert (end_left1 == start_middle1 and end_left2 == start_middle2
                and end_middle1 == start_right1 and end_middle2 == start_right2), \
            "The opcode boundary invariant does not hold."

        if not (tag_left == "equal" and (tag_middle == "delete" or tag_middle == "insert") and tag_right == "equal"):
            return (index, next_index)

        if tag_middle == "delete":
            (best_offset, _) = ShiftFilter.get_best_alignment(s1,
                                                              start_left1, start_middle1,
                                                              end_middle1, end_right1)
        elif tag_middle == "insert":
            (best_offset, _) = ShiftFilter.get_best_alignment(s2,
                                                              start_left2, start_middle2,
                                                              end_middle2, end_right2)
        else:
            assert False, "Invalid opcode tag."

        end_left1 += best_offset
        end_left2 += best_offset

        start_middle1 += best_offset
        start_middle2 += best_offset
        end_middle1 += best_offset
        end_middle2 += best_offset

        start_right1 += best_offset
        start_right2 += best_offset

        oc_left = (tag_left, start_left1, end_left1, start_left2, end_left2)
        oc_middle = (tag_middle, start_middle1, end_middle1, start_middle2, end_middle2)
        oc_right = (tag_right, start_right1, end_right1, start_right2, end_right2)

        # The entire left equality region has been consumed.
        if start_left1 == end_left1 and start_left2 == end_left2:

            opcodes[index - 2] = oc_middle
            opcodes[index - 1] = oc_right
            index -= 1

            # Attempt to merge with whatever was to the left of the equality region.
            if index >= 2 and ShiftFilter.merge(opcodes, index - 1) == index - 2:

                opcodes[index - 1] = oc_right
                index -= 1

                # Attempt shifts retroactively by taking into account the newly merged difference region.
                if index >= 2:
                    (index, _) = ShiftFilter.shift(opcodes, s1, s2, index, len(opcodes) - 1)

        # The entire right equality region has been consumed.
        elif start_right1 == end_right1 and start_right2 == end_right2:

            opcodes[index - 2] = oc_left
            opcodes[index - 1] = oc_middle
            index -= 1

            # Attempt to merge with whatever was to the right of the equality region.
            if next_index < len(opcodes) - 1:

                opcodes[index + 1] = opcodes[next_index + 1]

                if ShiftFilter.merge(opcodes, index + 1) == index:
                    next_index += 1

        # Both equality regions may have been modified; neither has been consumed in its entirety.
        else:
            opcodes[index - 2] = oc_left
            opcodes[index - 1] = oc_middle
            opcodes[index] = oc_right

        return (index, next_index)

    @staticmethod
    def get_best_alignment(s, start_left, start_middle, end_middle, end_right):
        """Gets the best alignment for the given difference region over its respective string.

        Args:
            s: The string.
            start_left: The left start index.
            start_middle: The middle start index (= the left end index).
            end_middle: The middle end index (= the right start index).
            end_right: The right end index.

        Returns:
            A 2-tuple containing the best alignment offset relative to the middle start index and the best score.
        """

        len_middle = end_middle - start_middle

        start_align = start_middle

        while start_align - 1 >= start_left and s[start_align - 1] == s[start_align - 1 + len_middle]:
            start_align -= 1

        end_align = end_middle

        while end_align < end_right and s[end_align] == s[end_align - len_middle]:
            end_align += 1

        (best_index, best_score) = (start_align, (0, 0))

        # Assign the maximum score if the entire left equality region has been consumed.
        if start_align == start_left:
            return (start_left - start_middle, (5, 0))

        # Assign the maximum score if the entire right equality region has been consumed.
        if end_align == end_right:
            return (end_right - len_middle - start_middle, (0, 5))

        for (i, i_left, i_right) in [(i, i - 1, i + len_middle) for i
                                     in range(max(start_align, start_left + 1),
                                              min(end_align, end_right - 1) - len_middle + 1)]:

            # Assign a score for the difference region boundary start.
            if s[i_left] == b"\n"[0]:

                if s[i_left + 1] == b"\n"[0]:
                    start_score = 4
                else:
                    start_score = 3

            elif ShiftFilter.whitespace_pattern.search(s[i_left:(i_left + 1)]):
                start_score = 2
            elif ShiftFilter.not_alphanumeric_pattern.search(s[i_left:(i_left + 1)]):
                start_score = 1
            else:
                start_score = 0

            # Assign a score for the difference region boundary end.
            if s[i_right] == b"\n"[0]:

                if s[i_right - 1] == b"\n"[0]:
                    end_score = 4
                else:
                    end_score = 3

            elif ShiftFilter.whitespace_pattern.search(s[i_right:(i_right + 1)]):
                end_score = 2
            elif ShiftFilter.not_alphanumeric_pattern.search(s[i_right:(i_right + 1)]):
                end_score = 1
            else:
                end_score = 0

            score = (start_score, end_score)
            (sorted_score, sorted_best_score) = (sorted(score, reverse=True), sorted(best_score, reverse=True))

            # Compare sorted score tuples lexicographically.
            if sorted_score > sorted_best_score or (sorted_score == sorted_best_score and score > best_score):
                (best_index, best_score) = (i, score)

        return (best_index - start_middle, best_score)

class EfficiencyFilter(MergeFilter):
    """An implementation of OpcodeFilter for optimizing the objective function (o * c + n), as described by
    http://neil.fraser.name/writing/diff/ in Section 3.1. Here, "o" is the number of edits, "c" is a tradeoff factor,
    and "n" is the total number of characters contained in edits. Note that a smaller value for "c" favors keeping
    difference regions the way they are, while a larger value favors agglomerating them with small equality regions in
    an attempt to improve human readability.
    """

    def __init__(self, tradeoff=4):
        """Default constructor.

        Args:
            tradeoff: The efficiency tradeoff factor for weighing edit cost against edit size.
        """
        super(EfficiencyFilter, self).__init__()

        self.tradeoff = tradeoff

    def __call__(self, opcodes, s1, s2):

        (edit_balance, mark_index) = (0, -1)

        for i in range(len(opcodes) - 2):

            (oc_left, oc_middle, oc_right) = opcodes[i:(i + 3)]
            (tag_left, tag_right) = (oc_left[0], oc_right[0])
            (tag_middle, start_middle1, end_middle1, start_middle2, end_middle2) = oc_middle

            if not (tag_left != "equal" and tag_middle == "equal" and tag_right != "equal"):
                continue

            edit_cost_continue = edit_cost_restart = 2

            if tag_left != "replace":
                edit_cost_restart -= 1

            if tag_right != "replace":
                edit_cost_continue -= 1
                edit_cost_restart -= 1

            edit_cost_continue *= self.tradeoff
            edit_cost_restart *= self.tradeoff
            edit_size = end_middle1 - start_middle1 + end_middle2 - start_middle2

            # If the edit balance from discarding and restarting is less than the edit balance from accumulating, then
            # let that be the new edit balance and reposition the mark index.
            if mark_index == -1 or edit_size - edit_cost_restart <= edit_balance + edit_size - edit_cost_continue:
                (edit_balance, mark_index) = (edit_size - edit_cost_restart, i)
            else:
                edit_balance += edit_size - edit_cost_continue

            # A negative edit balance minimizes the efficiency score. Reassign all opcodes from the mark to the current
            # index as replacement opcodes.
            if edit_balance < 0:
                opcodes[mark_index:(i + 3)] = [("replace", opcode[1], opcode[2], opcode[3], opcode[4])
                                               for opcode in opcodes[mark_index:(i + 3)]]
                (edit_balance, mark_index) = (0, -1)

        return super(EfficiencyFilter, self).__call__(opcodes, s1, s2)

class WordFilter(MergeFilter):
    """An implementation of OpcodeFilter for augmenting difference regions to stop at word boundaries, as defined by
    some regular expression. This transformation results in more semantically coherent, human-readable changes at the
    cost of shortest edit sequence optimality.
    """

    class Node(object):
        """A linked list node data structure.
        """

        def __init__(self, prev_node=None, next_node=None, payload=None):
            """Default constructor.

            Args:
                prev_node: The previous node.
                next_node: The next node.
                payload: The opcode payload.
            """
            super(WordFilter.Node, self).__init__()

            self.prev_node = prev_node
            self.next_node = next_node
            self.payload = payload

        def __iter__(self):

            curr = self

            while curr.next_node != self:
                curr = curr.next_node
                yield curr.payload

    def __init__(self, word_pattern=re.compile(b"[a-zA-Z0-9]+")):
        """Default constructor.

        Args:
            word_pattern: The regular expression for determining word boundaries.
        """
        super(WordFilter, self).__init__()

        self.word_pattern = word_pattern

    def __call__(self, opcodes, s1, s2):

        # Create a linked list of opcodes.

        head = WordFilter.Node()
        head.prev_node = head.next_node = curr = head

        for opcode in opcodes:
            curr.next_node = head.prev_node = curr = WordFilter.Node(curr, head, opcode)

        #

        word_bounds1 = [(m.start(0), m.end(0)) for m in self.word_pattern.finditer(s1)]
        word_bounds2 = [(m.start(0), m.end(0)) for m in self.word_pattern.finditer(s2)]

        WordFilter.split_equality_opcodes(head, word_bounds1)
        WordFilter.split_equality_opcodes(head, word_bounds2, True)

        nodes_map1 = WordFilter.create_opcodes_map(head, word_bounds1)
        nodes_map2 = WordFilter.create_opcodes_map(head, word_bounds2, True)

        word_breaks1 = list(chain.from_iterable(word_bounds1))
        word_breaks2 = list(chain.from_iterable(word_bounds2))

        for i in range(0, len(word_breaks1), 2):
            WordFilter.augment_diff_regions(i, word_breaks1, word_breaks2, nodes_map1, nodes_map2)

        for i in range(0, len(word_breaks2), 2):
            WordFilter.augment_diff_regions(i, word_breaks1, word_breaks2, nodes_map1, nodes_map2, inverted=True)

        # Don't forget to merge artificially split equality regions and recently created replacement regions.
        return super(WordFilter, self).__call__(list(head), s1, s2)

    @staticmethod
    def split_equality_opcodes(head, word_bounds, inverted=False):
        """Splits equality opcodes at word boundaries.

        Args:
            head: The opcode linked list head node.
            word_bounds: The word boundaries of the form [(start_1, end_1), ..., (start_n, end_n)].
            inverted: Whether opcodes should be considered from the second string's perspective.
        """

        if not inverted:
            tuple_offset = 1
        else:
            tuple_offset = 3

        (curr, word_index, nwords) = (head, 0, len(word_bounds))

        while curr.next_node != head:

            curr = curr.next_node
            oc_current = curr.payload

            while word_index < nwords:

                (start, end) = word_bounds[word_index]
                (tag, oc_start, oc_end) = (oc_current[0], oc_current[tuple_offset], oc_current[tuple_offset + 1])

                if tag == "equal":

                    # Split the end of the current opcode.
                    if oc_start < start and oc_end > start:
                        offset = start - oc_start
                        (_, oc_start1, oc_end1, oc_start2, oc_end2) = oc_current
                        oc1 = ("equal", oc_start1, oc_start1 + offset, oc_start2, oc_start2 + offset)
                        oc2 = oc_current = ("equal", oc_start1 + offset, oc_end1, oc_start2 + offset, oc_end2)
                        node1 = WordFilter.Node(curr.prev_node, None, oc1)
                        node2 = WordFilter.Node(None, curr.next_node, oc2)
                        curr.prev_node.next_node = node2.prev_node = node1
                        curr.next_node.prev_node = node1.next_node = curr = node2

                    # Split the beginning of the current opcode.
                    if oc_start < end and oc_end > end:
                        offset = oc_end - end
                        (_, oc_start1, oc_end1, oc_start2, oc_end2) = oc_current
                        oc1 = ("equal", oc_start1, oc_end1 - offset, oc_start2, oc_end2 - offset)
                        oc2 = oc_current = ("equal", oc_end1 - offset, oc_end1, oc_end2 - offset, oc_end2)
                        node1 = WordFilter.Node(curr.prev_node, None, oc1)
                        node2 = WordFilter.Node(None, curr.next_node, oc2)
                        curr.prev_node.next_node = node2.prev_node = node1
                        curr.next_node.prev_node = node1.next_node = curr = node2

                if oc_end > end:
                    word_index += 1
                else:
                    break

    @staticmethod
    def create_opcodes_map(head, word_bounds, inverted=False):
        """Creates a mapping from words to linked list nodes whose opcode payloads they intersect.

        Args:
            head: The opcode linked list head node.
            word_bounds: The word boundaries of the form [(start_1, end_1), ..., (start_n, end_n)].
            inverted: Whether opcodes should be considered from the second string's perspective.

        Returns:
            A mapping from words to linked list nodes.
        """

        nodes_map = dict([((start, end), []) for (start, end) in word_bounds])

        if not inverted:
            tuple_offset = 1
        else:
            tuple_offset = 3

        (curr, word_index, nwords) = (head, 0, len(word_bounds))

        while curr.next_node != head:

            curr = curr.next_node
            oc_current = curr.payload

            while word_index < nwords:

                (start, end) = word_bounds[word_index]
                (tag, oc_start, oc_end) = (oc_current[0], oc_current[tuple_offset], oc_current[tuple_offset + 1])

                # Include the node if it has an intersecting opcode payload.
                if oc_start < end and oc_end > start:

                    assert tag != "equal" or (oc_start >= start and oc_end <= end), \
                        "The equality opcode containment invariant does not hold."

                    nodes_map[(start, end)].append(curr)

                if oc_end > end:
                    word_index += 1
                else:
                    break

        return nodes_map

    @staticmethod
    def augment_diff_regions(index, word_breaks1, word_breaks2, nodes_map1, nodes_map2, inverted=False):
        """Augments difference regions to include whole words. This entails reassigning equality opcodes found in words
        with nontrivial changes as replacement opcodes.

        Args:
            index: The word break index to consider.
            word_breaks1: The word breaks of the first string of the form [start_1, end_1, ..., start_n, end_n].
            word_breaks2: The word breaks of the second string.
            nodes_map1: The mapping of the first string's words to linked list nodes.
            nodes_map2: The mapping of the second string's words to linked list nodes.
            inverted: Whether opcodes should be considered from the second string's perspective.
        """

        if not inverted:
            (nodes, word_breaks_inverse) = (nodes_map1[tuple(word_breaks1[index:(index + 2)])], word_breaks2)
            (tuple_offset, tuple_offset_inverse) = (1, 3)
        else:
            (nodes, word_breaks_inverse) = (nodes_map2[tuple(word_breaks2[index:(index + 2)])], word_breaks1)
            (tuple_offset, tuple_offset_inverse) = (3, 1)

        # No intraword edits found -- Return immediately.
        if not [opcode for opcode
                in [node.payload for node in nodes]
                if opcode[0] != "equal" and opcode[tuple_offset] != opcode[tuple_offset + 1]]:
            return

        node = opcode = None

        # Reassign all equality opcodes as replacement opcodes, thus including the entire word in a difference region.
        for (node, opcode) in [(node, opcode) for (node, opcode)
                               in [(node, node.payload) for node in nodes] if opcode[0] == "equal"]:

            node.payload = ("replace", opcode[1], opcode[2], opcode[3], opcode[4])

            (start_inverse, end_inverse) = (opcode[tuple_offset_inverse], opcode[tuple_offset_inverse + 1])
            index_inverse = 2 * ((bisect.bisect_right(word_breaks_inverse, start_inverse) - 1) // 2)

            assert (start_inverse >= word_breaks_inverse[index_inverse]
                    and end_inverse <= word_breaks_inverse[index_inverse + 1]), \
                "The equality opcode containment invariant does not hold."

            WordFilter.augment_diff_regions(index_inverse,
                                            word_breaks1, word_breaks2, nodes_map1, nodes_map2, not inverted)

#----------------------------------------------------------------------------------------------------------------------#
# Main program.                                                                                                        #
#----------------------------------------------------------------------------------------------------------------------#

NO_NEWLINE = b"\\ No newline at end of file"

# Some ANSI color escape codes.
ANSI_RESET = b"\033[m"
ANSI_RED = b"\033[0;31m"
ANSI_GREEN = b"\033[0;32m"
ANSI_RED_UNDERLINE = b"\033[4;31m"
ANSI_GREEN_UNDERLINE = b"\033[4;32m"
ANSI_BOLD_BLACK = b"\033[1;30m"
ANSI_TEAL = b"\033[0;36m"

hunk_header_pattern = re.compile(b"^(?P<head>@@"
                                 b" -(?:[1-9][0-9]*|0)(?:,(?P<nlines1>[1-9][0-9]*|0))?"
                                 b" \\+(?:[1-9][0-9]*|0)(?:,(?P<nlines2>[1-9][0-9]*|0))?"
                                 b" @@)(?P<tail>.*)$")
hunk_line_pattern = re.compile(b"^[ \\-\\+\\\\]")

identity_filter = IdentityFilter()
merge_filter = MergeFilter()
shift_filter = ShiftFilter()

# Create facades to ensure compatibility with major versions 2 and 3.
if sys.version_info[0] == 3:
    stdin = getattr(sys.stdin, "buffer")
    stdout = getattr(sys.stdout, "buffer")
    decode = lambda b: b.decode("utf-8")
    encode = lambda s: s.encode("utf-8")
else:
    stdin = sys.stdin
    stdout = sys.stdout
    decode = encode = lambda s: s

def main():
    """The main method body.
    """

    parser = ArgumentParser()
    parser.add_argument("-c", "--color", dest="color_mode", nargs="?", const="always", default="auto",
                        help="the color mode, one of {always, auto, never}")
    parser.add_argument("-r", "--regex", dest="word_filter",
                        type=lambda s: WordFilter(word_pattern=re.compile(encode(s))),
                        default=WordFilter(), metavar="REGEX",
                        help="the regular expression for determining word boundaries"
                        " (tweaks human readability)")
    parser.add_argument("-t", "--tradeoff", dest="efficiency_filter",
                        type=lambda s: EfficiencyFilter(tradeoff=int(s)),
                        default=EfficiencyFilter(), metavar="TRADEOFF",
                        help="the efficiency tradeoff factor for weighing edit cost against edit size"
                        " (tweaks human readability)")

    args = parser.parse_args()

    if args.color_mode not in ["always", "auto", "never"]:
        raise RuntimeError("Please provide a color mode that is one of {always, auto, never}.")

    #

    if (args.color_mode == "auto" and stdout.isatty()) or args.color_mode == "always":

        opcode_filter = ChainFilter(shift_filter, args.word_filter, args.efficiency_filter)

        minus = ANSI_RED + b"-" + ANSI_RESET
        plus = ANSI_GREEN + b"+" + ANSI_RESET
        equal = b" "

        def filter_hunk(lines):

            lines1 = []
            lines2 = []

            no_newline1 = no_newline2 = False

            for i in range(len(lines)):

                (status, content) = (lines[i][0], lines[i][1:])

                if status == b"-"[0]:
                    lines1.append(content)
                elif status == b"+"[0]:
                    lines2.append(content)
                elif status == b" "[0]:
                    lines1.append(content)
                    lines2.append(content)
                elif status == b"\\"[0]:

                    if content != NO_NEWLINE[1:]:
                        raise RuntimeError("The line beginning with \"\\\" must read \"{0}\"."
                                           .format(decode(NO_NEWLINE).replace("\"", "\\\"")))

                    prev_status = lines[i - 1][0]

                    if prev_status == b"-"[0]:
                        no_newline1 = True
                    elif prev_status == b"+"[0]:
                        no_newline2 = True
                    elif prev_status == b" "[0]:

                        if i != len(lines) - 1:
                            raise RuntimeError("The line \"{0}\" must be the last line."
                                               .format(decode(NO_NEWLINE).replace("\"", "\\\"")))

                        no_newline1 = no_newline2 = True

                    else:
                        raise RuntimeError("Invalid line status.")

                else:
                    raise RuntimeError("Invalid line status.")

            matches = list(colorize_hunk(lines1, lines2, opcode_filter=opcode_filter))

            # Reassign terminal equality lines to adjacent matching sets of difference lines if they end with newlines
            # in the first text, but not in the second.

            last_index1 = last_index2 = 0

            for i in range(-1, -len(matches) - 1, -1):

                match = matches[i]

                if len(match) == 1 or (len(match) == 2 and match[0]):
                    last_index1 = i
                    break

            for i in range(-1, -len(matches) - 1, -1):

                match = matches[i]

                if len(match) == 1 or (len(match) == 2 and match[1]):
                    last_index2 = i
                    break

            if (no_newline1 and len(matches[last_index1]) == 1) != (no_newline2 and len(matches[last_index2]) == 1):

                if no_newline1 and len(matches[last_index1]) == 1:

                    (lines,) = matches[last_index1]

                    if last_index1 == -2:
                        next_match = matches[-1]
                        next_match = matches[-1] = ([lines[-1]] + next_match[0], [lines[-1]] + next_match[1])
                    elif last_index1 == -1:
                        next_match = ([lines[-1]], [lines[-1]])
                        matches.append(next_match)
                    else:
                        assert False, "Invalid index."

                    del lines[-1]

                    if not lines:

                        del matches[-2]

                        if len(matches) >= 2:
                            prev_match = matches[-2]
                            next_match = matches[-1] = (prev_match[0] + next_match[0], prev_match[1] + next_match[1])
                            del matches[-2]

                if no_newline2 and len(matches[last_index2]) == 1:

                    (lines,) = matches[last_index2]

                    if last_index2 == -2:
                        next_match = matches[-1]
                        next_match = matches[-1] = ([lines[-1]] + next_match[0], [lines[-1]] + next_match[1])
                    elif last_index2 == -1:
                        next_match = ([lines[-1]], [lines[-1]])
                        matches.append(next_match)
                    else:
                        assert False, "Invalid index."

                    del lines[-1]

                    if not lines:

                        del matches[-2]

                        if len(matches) >= 2:
                            prev_match = matches[-2]
                            next_match = matches[-1] = (prev_match[0] + next_match[0], prev_match[1] + next_match[1])
                            del matches[-2]

            # Emit the colorized hunk.

            lines = []

            for i in range(len(matches) - 1):

                match = matches[i]

                if len(match) == 1:
                    lines.extend([equal + line for line in match[0]])
                elif len(match) == 2:
                    lines.extend([minus + line for line in match[0]])
                    lines.extend([plus + line for line in match[1]])
                else:
                    assert False, "Invalid tuple length."

            if matches:

                match = matches[-1]

                if len(match) == 1:

                    assert no_newline1 == no_newline2, "Missing EOF newlines must occur in both texts or neither."

                    lines.extend([equal + line for line in match[0]])

                    if no_newline1 and no_newline2:
                        lines.append(NO_NEWLINE)

                elif len(match) == 2:

                    lines.extend([minus + line for line in match[0]])

                    if no_newline1:
                        lines.append(NO_NEWLINE)

                    lines.extend([plus + line for line in match[1]])

                    if no_newline2:
                        lines.append(NO_NEWLINE)

                else:
                    assert False, "Invalid tuple length."

            return lines

        def filter_file_header(line):
            return ANSI_BOLD_BLACK + line + ANSI_RESET

        def filter_hunk_header(line):
            m = hunk_header_pattern.search(line)
            return ANSI_TEAL + m.group("head") + ANSI_RESET + m.group("tail")

    else:
        filter_hunk = filter_file_header = filter_hunk_header = lambda l: l

    hunk_lines = []

    def flush():

        for line in filter_hunk(hunk_lines):
            stdout.write(line + b"\n")

        stdout.flush()

        del hunk_lines[:]

    #

    nlines1 = nlines2 = 0

    for line in [line.rstrip(b"\n") for line in stdin]:

        if nlines1 == 0 and nlines2 == 0:

            m = hunk_header_pattern.search(line)

            if m:

                (nlines1, nlines2) = (m.group("nlines1", "nlines2"))

                if nlines1 is None:
                    nlines1 = b"1"

                if nlines2 is None:
                    nlines2 = b"1"

                (nlines1, nlines2) = (int(nlines1), int(nlines2))

                flush()
                stdout.write(filter_hunk_header(line) + b"\n")

            elif line == NO_NEWLINE:
                hunk_lines.append(line)
            else:
                flush()
                stdout.write(filter_file_header(line) + b"\n")

        else:

            if line[0] == b"-"[0]:
                nlines1 -= 1
            elif line[0] == b"+"[0]:
                nlines2 -= 1
            elif line[0] == b" "[0]:
                nlines1 -= 1
                nlines2 -= 1

            hunk_lines.append(line)

    flush()

#----------------------------------------------------------------------------------------------------------------------#
# Colorization routines.                                                                                               #
#----------------------------------------------------------------------------------------------------------------------#

def colorize_hunk(lines1, lines2, opcode_filter=identity_filter):
    """Colorizes the given hunk.

    Args:
        lines1: The lines of the first text.
        lines2: The lines of the second text.
        opcode_filter: The OpcodeFilter to use for post-processing.

    Returns:
        A generator of alternating 2-tuples and 1-tuples containing matching sets of colorized difference lines and
        plain equality lines, respectively.
    """

    if lines1 and not lines2:
        yield (list(colorize("delete", lines1, [[("delete", 0, len(line))] for line in lines1])), [])
        return
    elif not lines1 and lines2:
        yield ([], list(colorize("insert", lines2, [[("insert", 0, len(line))] for line in lines2])))
        return
    elif not lines1 and not lines2:
        return

    s1 = b"\n".join(lines1) + b"\n"
    s2 = b"\n".join(lines2) + b"\n"

    opcodes = opcode_filter(myers_diff(s1, s2), s1, s2)

    s1 = b"\n" + s1 + b"\0"
    s2 = b"\n" + s2 + b"\0"

    (line_breaks1, index1, index_save1) = (list(get_line_breaks(lines1)), 0, 0)
    (line_breaks2, index2, index_save2) = (list(get_line_breaks(lines2)), 0, 0)

    nlines1 = len(lines1)
    nlines2 = len(lines2)

    opcodes1 = [[] for _ in range(nlines1)]
    opcodes2 = [[] for _ in range(nlines2)]

    for (tag, oc_start1, oc_end1, oc_start2, oc_end2) in opcodes:

        index_eq1 = index_eq2 = index_eq_save1 = index_eq_save2 = -1

        while True:

            (start, end) = (line_breaks1[index1], line_breaks1[index1 + 1])

            opcodes1[index1].append((tag, max(oc_start1, start) - start, min(oc_end1, end - 1) - start))

            if oc_end1 >= end - 1:

                # Check for entire lines contained in equality opcodes.
                if (tag == "equal"
                    and (oc_start1 < start or (oc_start1 == start and s2[oc_start2] == b"\n"[0]))
                    and (oc_end1 >= end or (oc_end1 == end - 1 and s2[oc_end2 + 1] == b"\n"[0]))):

                    if index_eq_save1 == -1:
                        index_eq_save1 = index1

                    index_eq1 = index1 + 1

                if oc_end1 > end:
                    index1 += 1
                else:
                    break

            else:
                break

        while True:

            (start, end) = (line_breaks2[index2], line_breaks2[index2 + 1])

            opcodes2[index2].append((tag, max(oc_start2, start) - start, min(oc_end2, end - 1) - start))

            if oc_end2 >= end - 1:

                # Check for entire lines contained in equality opcodes.
                if (tag == "equal"
                    and (oc_start2 < start or (oc_start2 == start and s1[oc_start1] == b"\n"[0]))
                    and (oc_end2 >= end or (oc_end2 == end - 1 and s1[oc_end1 + 1] == b"\n"[0]))):

                    if index_eq_save2 == -1:
                        index_eq_save2 = index2

                    index_eq2 = index2 + 1

                if oc_end2 > end:
                    index2 += 1
                else:
                    break

            else:
                break

        if index_eq1 != -1 and index_eq2 != -1:

            # Deal with spurious, leading difference lines arising from opcodes that don't end at newline characters.
            if (index_eq_save1 - index_save1 > 0 and index_eq_save2 - index_save2 > 0
                and lines1[index_save1] == lines2[index_save2]):
                yield([lines1[index_save1]],)
                index_save1 += 1
                index_save2 += 1

            # Yield accumulated difference lines.
            if index_eq_save1 - index_save1 > 0 or index_eq_save2 - index_save2 > 0:
                yield (list(colorize("delete",
                                     lines1[index_save1:index_eq_save1], opcodes1[index_save1:index_eq_save1])),
                       list(colorize("insert",
                                     lines2[index_save2:index_eq_save2], opcodes2[index_save2:index_eq_save2])))

            equality_lines1 = lines1[index_eq_save1:index_eq1]
            equality_lines2 = lines2[index_eq_save2:index_eq2]

            assert equality_lines1 == equality_lines2, "Equality lines of the first and second texts do not match."

            # Yield accumulated equality lines.
            yield (equality_lines1,)

            index_save1 = index_eq1
            index_save2 = index_eq2

        else:
            assert index_eq1 == -1 and index_eq2 == -1, "Equality lines must be found in both texts or neither."

    # Deal with spurious, leading difference lines arising from opcodes that don't end at newline characters.
    if index_save1 < len(lines1) and index_save2 < len(lines2) and lines1[index_save1] == lines2[index_save2]:
        yield([lines1[index_save1]],)
        index_save1 += 1
        index_save2 += 1

    # Yield any remaining, accumulated difference lines.
    if nlines1 - index_save1 > 0 or nlines2 - index_save2 > 0:
        yield (list(colorize("delete", lines1[index_save1:nlines1], opcodes1[index_save1:nlines1])),
               list(colorize("insert", lines2[index_save2:nlines2], opcodes2[index_save2:nlines2])))

def get_line_breaks(lines):
    """Calculates line breaks from the given lines in support of colorize_hunk().

    Args:
        lines: The lines.

    Returns:
        A generator of line breaks.
    """

    n_chars = 0
    yield n_chars

    for line in lines:
        n_chars += len(line) + 1
        yield n_chars

def colorize(mode, lines, line_opcodes):
    """Colorizes the given lines.

    Args:
        mode: The mode of operation, "delete" or "insert".
        lines: The lines to colorize.
        line_opcodes: The (mini) opcodes containing intraline edits.

    Returns:
        A generator of colorized lines.
    """

    for (line, opcodes) in zip(lines, line_opcodes):

        if sum([end - start for (tag, start, end) in opcodes if tag == mode or tag == "replace"]) < len(line):

            adjustment = 0

            for (tag, start, end) in [(tag, start, end) for (tag, start, end) in opcodes if start != end]:

                if mode == "delete" and (tag == "replace" or tag == "delete"):
                    color = ANSI_RED_UNDERLINE
                elif mode == "insert" and (tag == "replace" or tag == "insert"):
                    color = ANSI_GREEN_UNDERLINE
                else:
                    continue

                line = (line[:(start + adjustment)]
                        + color
                        + line[(start + adjustment):(end + adjustment)]
                        + ANSI_RESET
                        + line[(end + adjustment):])
                adjustment += len(color) + len(ANSI_RESET)

        else:

            if mode == "delete":
                color = ANSI_RED
            elif mode == "insert":
                color = ANSI_GREEN
            else:
                assert False, "Invalid mode."

            line = color + line + ANSI_RESET

        yield line

#----------------------------------------------------------------------------------------------------------------------#
# Myer's diff algorithm.                                                                                               #
#----------------------------------------------------------------------------------------------------------------------#

def myers_diff(s1, s2, offset1=0, offset2=0):
    """Uses the middle snake algorithm of myers_diff_bisect() to create edit script opcodes.

    Args:
        s1: The first string.
        s2: The second string.
        offset1: The offset of the first string in the original (internal use only).
        offset2: The offset of the second string in the original (internal use only).

    Returns:
        A list of opcodes of the form (tag, start1, end1, start2, end2), where start{1, 2} and end{1, 2} are starting
        and ending indices for the regions affected. The tag can be one of {"delete", "insert", "equal", "replace"}.
        Note that these opcodes are styled after those used by the difflib library.
    """

    opcodes = []

    if s1 and not s2:
        opcodes.append(("delete", offset1, offset1 + len(s1), offset2, offset2))
    elif not s1 and s2:
        opcodes.append(("insert", offset1, offset1, offset2, offset2 + len(s2)))
    elif s1 == s2:
        opcodes.append(("equal", offset1, offset1 + len(s1), offset2, offset2 + len(s2)))
    else:

        (ind1, ind2) = myers_diff_bisect(s1, s2)

        # Insert a "replace" opcode if the bisection is trivial.
        if ind1 == 0 and ind2 == 0:
            opcodes.append(("replace", offset1, offset1 + len(s1), offset2, offset2 + len(s2)))
        # Perform the bisection and recurse.
        else:
            opcodes.extend(myers_diff(s1[:ind1], s2[:ind2], offset1, offset2))
            opcodes.extend(myers_diff(s1[ind1:], s2[ind2:], offset1 + ind1, offset2 + ind2))

    return merge_filter(opcodes, s1, s2)

def myers_diff_bisect(s1, s2):
    """An implementation of Myers' diff algorithm with linear space refinement, which is described in the 1986 paper,
    "An O(ND) Difference Algorithm and its Variations".

    Args:
        s1: The first string.
        s2: The second string.

    Returns:
        A 2-tuple containing the bisection indices of the first and second strings.
    """

    l1 = len(s1)
    l2 = len(s2)

    delta = l1 - l2

    # Trim common prefixes and suffixes for speed and to ensure a nontrivial bisection.

    prefix_offset = 0

    while prefix_offset < l1 and prefix_offset < l2 and s1[prefix_offset] == s2[prefix_offset]:
        prefix_offset += 1

    suffix_offset = 0

    while suffix_offset < l1 and suffix_offset < l2 and s1[-suffix_offset - 1] == s2[-suffix_offset - 1]:
        suffix_offset += 1

    s1 = s1[prefix_offset:(l1 - suffix_offset)]
    s2 = s2[prefix_offset:(l2 - suffix_offset)]

    l1 = len(s1)
    l2 = len(s2)

    # Set up an imaginary "D = -1" inductive base case.

    frontier_forward = [None] * (2 * ((l1 + l2 + 1) // 2) + 1)

    if len(frontier_forward) > 1:
        frontier_forward[-1] = (-1, 0)
        frontier_forward[1] = (0, -1)

    frontier_backward = frontier_forward[:]

    frontier_range = (-(l1 + l2 + 1) // 2, (l1 + l2 + 1) // 2 + 1)

    #

    range_adj_forward = (0, 0)
    range_adj_backward = (0, 0)

    for d in range((l1 + l2 + 1) // 2):

        range_forward = (-d + range_adj_forward[0], d + 1 - range_adj_forward[1])
        range_backward = (-d + range_adj_backward[0], d + 1 - range_adj_backward[1])

        # Inductive step: Each furthest reaching D-path is composed of a (D - 1)-path, followed by a vertical or
        # horizontal edge, followed by the longest possible snake (sequence of diagonal edges).

        # Build D-paths from (D - 1)-paths in the forward direction.
        for k in range(range_forward[0], range_forward[1], 2):

            if frontier_forward[k - 1]:
                endpoint_minus = (frontier_forward[k - 1][0] + 1, frontier_forward[k - 1][1])
            else:
                endpoint_minus = None

            if frontier_forward[k + 1]:
                endpoint_plus = (frontier_forward[k + 1][0], frontier_forward[k + 1][1] + 1)
            else:
                endpoint_plus = None

            # Prefer endpoints furthest from the origin by Manhattan distance.
            if endpoint_minus and endpoint_plus:
                if sum(endpoint_minus) > sum(endpoint_plus):
                    (x, y) = endpoint_minus
                else:
                    (x, y) = endpoint_plus
            elif endpoint_minus:
                (x, y) = endpoint_minus
            elif endpoint_plus:
                (x, y) = endpoint_plus
            else:
                assert False, "Control should never reach here."

            # Prune the search range if falling out of bounds.

            if x > l1:
                range_adj_forward = (range_adj_forward[0], range_adj_forward[1] + 2)
                continue

            if y > l2:
                range_adj_forward = (range_adj_forward[0] + 2, range_adj_forward[1])
                continue

            # Move the frontier forward for each match.
            while x < l1 and y < l2 and s1[x] == s2[y]:
                x += 1
                y += 1

            frontier_forward[k] = (x, y)

            # First overlap will occur in the forward direction if delta is odd.
            if delta % 2 == 1:

                k_backward = delta - k

                if (k_backward >= frontier_range[0] and k_backward < frontier_range[1]
                    and frontier_backward[k_backward]):

                    # Translate backward coordinates to forward coordinates and check for overlap.
                    (x_backward, y_backward) = frontier_backward[k_backward]
                    (x_transformed, y_transformed) = (l1 - x_backward, l2 - y_backward)

                    if x >= x_transformed and y >= y_transformed:
                        return (x + prefix_offset, y + prefix_offset)

        # Build D-paths from (D - 1)-paths in the backward direction.
        for k in range(range_backward[0], range_backward[1], 2):

            if frontier_backward[k - 1]:
                endpoint_minus = (frontier_backward[k - 1][0] + 1, frontier_backward[k - 1][1])
            else:
                endpoint_minus = None

            if frontier_backward[k + 1]:
                endpoint_plus = (frontier_backward[k + 1][0], frontier_backward[k + 1][1] + 1)
            else:
                endpoint_plus = None

            # Prefer endpoints furthest from the origin by Manhattan distance.
            if endpoint_minus and endpoint_plus:
                if sum(endpoint_minus) > sum(endpoint_plus):
                    (x, y) = endpoint_minus
                else:
                    (x, y) = endpoint_plus
            elif endpoint_minus:
                (x, y) = endpoint_minus
            elif endpoint_plus:
                (x, y) = endpoint_plus
            else:
                assert False, "Control should never reach here."

            # Prune the search range if falling out of bounds.

            if x > l1:
                range_adj_backward = (range_adj_backward[0], range_adj_backward[1] + 2)
                continue

            if y > l2:
                range_adj_backward = (range_adj_backward[0] + 2, range_adj_backward[1])
                continue

            # Move the frontier backward for each match.
            while x < l1 and y < l2 and s1[-x - 1] == s2[-y - 1]:
                x += 1
                y += 1

            frontier_backward[k] = (x, y)

            # First overlap will occur in the backward direction if delta is even.
            if delta % 2 == 0:

                k_forward = delta - k

                if (k_forward >= frontier_range[0] and k_forward < frontier_range[1]
                    and frontier_forward[k_forward]):

                    # Translate backward coordinates to forward coordinates and check for overlap.
                    (x_forward, y_forward) = frontier_forward[k_forward]
                    (x_transformed, y_transformed) = (l1 - x, l2 - y)

                    if x_forward >= x_transformed and y_forward >= y_transformed:
                        return (x_forward + prefix_offset, y_forward + prefix_offset)

    if prefix_offset > 0:
        return (prefix_offset, prefix_offset)
    elif suffix_offset > 0:
        return (prefix_offset + l1, prefix_offset + l2)
    else:
        return (0, 0)

#

if __name__ == "__main__":
    sys.exit(main())
