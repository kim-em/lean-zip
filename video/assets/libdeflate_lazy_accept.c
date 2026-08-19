/* Vendored from https://github.com/ebiggers/libdeflate
 * commit b122c8b, lib/deflate_compress.c lines 2694-2740 (MIT license,
 * see LICENSE-libdeflate in this directory). Used by the video's
 * C-to-Lean morph animation; do not edit. */
			/*
			 * Try to find a better match at the next position.
			 *
			 * Note: since we already have a match at the *current*
			 * position, we use only half the 'max_search_depth'
			 * when checking the *next* position.  This is a useful
			 * trade-off because it's more worthwhile to use a
			 * greater search depth on the initial match.
			 *
			 * Note: it's possible to structure the code such that
			 * there's only one call to longest_match(), which
			 * handles both the "find the initial match" and "try to
			 * find a better match" cases.  However, it is faster to
			 * have two call sites, with longest_match() inlined at
			 * each.
			 */
			adjust_max_and_nice_len(&max_len, &nice_len,
						in_end - in_next);
			next_len = hc_matchfinder_longest_match(
						&c->p.g.hc_mf,
						&in_cur_base,
						in_next++,
						cur_len - 1,
						max_len,
						nice_len,
						c->max_search_depth >> 1,
						next_hashes,
						&next_offset);
			if (next_len >= cur_len &&
			    4 * (int)(next_len - cur_len) +
			    ((int)bsr32(cur_offset) -
			     (int)bsr32(next_offset)) > 2) {
				/*
				 * Found a better match at the next position.
				 * Output a literal.  Then the next match
				 * becomes the current match.
				 */
				deflate_choose_literal(c, *(in_next - 2), true,
						       seq);
				cur_len = next_len;
				cur_offset = next_offset;
				goto have_cur_match;
			}

			if (lazy2) {
				/* In lazy2 mode, look ahead another position */
				adjust_max_and_nice_len(&max_len, &nice_len,
