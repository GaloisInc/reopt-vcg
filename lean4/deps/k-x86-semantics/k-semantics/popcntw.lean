def popcntw : instruction :=
  definst "popcntw" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      setRegister (lhs.of_reg r16_1) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 0 1)) (concat (expression.bv_nat 1 0) (extract v_3 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 2 3)) (concat (expression.bv_nat 1 0) (extract v_3 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 4 5)) (concat (expression.bv_nat 1 0) (extract v_3 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 6 7)) (concat (expression.bv_nat 1 0) (extract v_3 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 8 9)) (concat (expression.bv_nat 1 0) (extract v_3 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 10 11)) (concat (expression.bv_nat 1 0) (extract v_3 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 12 13)) (concat (expression.bv_nat 1 0) (extract v_3 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_3 14 15)) (concat (expression.bv_nat 1 0) (extract v_3 15 16)))))))));
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_0);
      setRegister (lhs.of_reg r16_1) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 0 1)) (concat (expression.bv_nat 1 0) (extract v_2 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 2 3)) (concat (expression.bv_nat 1 0) (extract v_2 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 4 5)) (concat (expression.bv_nat 1 0) (extract v_2 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 6 7)) (concat (expression.bv_nat 1 0) (extract v_2 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 8 9)) (concat (expression.bv_nat 1 0) (extract v_2 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 10 11)) (concat (expression.bv_nat 1 0) (extract v_2 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 12 13)) (concat (expression.bv_nat 1 0) (extract v_2 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_2 14 15)) (concat (expression.bv_nat 1 0) (extract v_2 15 16)))))))));
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end
