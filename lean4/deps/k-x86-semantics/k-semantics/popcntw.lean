def popcntw1 : instruction :=
  definst "popcntw" $ do
    pattern fun (v_2946 : reg (bv 16)) (v_2947 : reg (bv 16)) => do
      v_6389 <- getRegister v_2946;
      setRegister (lhs.of_reg v_2947) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 0 1)) (concat (expression.bv_nat 1 0) (extract v_6389 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 2 3)) (concat (expression.bv_nat 1 0) (extract v_6389 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 4 5)) (concat (expression.bv_nat 1 0) (extract v_6389 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 6 7)) (concat (expression.bv_nat 1 0) (extract v_6389 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 8 9)) (concat (expression.bv_nat 1 0) (extract v_6389 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 10 11)) (concat (expression.bv_nat 1 0) (extract v_6389 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 12 13)) (concat (expression.bv_nat 1 0) (extract v_6389 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6389 14 15)) (concat (expression.bv_nat 1 0) (extract v_6389 15 16)))))))));
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_6389);
      pure ()
    pat_end;
    pattern fun (v_2942 : Mem) (v_2943 : reg (bv 16)) => do
      v_13075 <- evaluateAddress v_2942;
      v_13076 <- load v_13075 2;
      setRegister (lhs.of_reg v_2943) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 0 1)) (concat (expression.bv_nat 1 0) (extract v_13076 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 2 3)) (concat (expression.bv_nat 1 0) (extract v_13076 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 4 5)) (concat (expression.bv_nat 1 0) (extract v_13076 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 6 7)) (concat (expression.bv_nat 1 0) (extract v_13076 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 8 9)) (concat (expression.bv_nat 1 0) (extract v_13076 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 10 11)) (concat (expression.bv_nat 1 0) (extract v_13076 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 12 13)) (concat (expression.bv_nat 1 0) (extract v_13076 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13076 14 15)) (concat (expression.bv_nat 1 0) (extract v_13076 15 16)))))))));
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_13076);
      pure ()
    pat_end
