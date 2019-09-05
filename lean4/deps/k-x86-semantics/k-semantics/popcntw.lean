def popcntw1 : instruction :=
  definst "popcntw" $ do
    pattern fun (v_2919 : reg (bv 16)) (v_2920 : reg (bv 16)) => do
      v_6362 <- getRegister v_2919;
      setRegister (lhs.of_reg v_2920) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 0 1)) (concat (expression.bv_nat 1 0) (extract v_6362 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 2 3)) (concat (expression.bv_nat 1 0) (extract v_6362 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 4 5)) (concat (expression.bv_nat 1 0) (extract v_6362 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 6 7)) (concat (expression.bv_nat 1 0) (extract v_6362 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 8 9)) (concat (expression.bv_nat 1 0) (extract v_6362 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 10 11)) (concat (expression.bv_nat 1 0) (extract v_6362 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 12 13)) (concat (expression.bv_nat 1 0) (extract v_6362 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6362 14 15)) (concat (expression.bv_nat 1 0) (extract v_6362 15 16)))))))));
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_6362);
      pure ()
    pat_end;
    pattern fun (v_2914 : Mem) (v_2915 : reg (bv 16)) => do
      v_13099 <- evaluateAddress v_2914;
      v_13100 <- load v_13099 2;
      setRegister (lhs.of_reg v_2915) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 0 1)) (concat (expression.bv_nat 1 0) (extract v_13100 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 2 3)) (concat (expression.bv_nat 1 0) (extract v_13100 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 4 5)) (concat (expression.bv_nat 1 0) (extract v_13100 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 6 7)) (concat (expression.bv_nat 1 0) (extract v_13100 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 8 9)) (concat (expression.bv_nat 1 0) (extract v_13100 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 10 11)) (concat (expression.bv_nat 1 0) (extract v_13100 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 12 13)) (concat (expression.bv_nat 1 0) (extract v_13100 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13100 14 15)) (concat (expression.bv_nat 1 0) (extract v_13100 15 16)))))))));
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_13100);
      pure ()
    pat_end
