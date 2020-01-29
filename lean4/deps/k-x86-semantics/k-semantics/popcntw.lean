def popcntw : instruction :=
  definst "popcntw" $ do
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      (v_4 : expression (bv 1)) <- eval (extract v_3 0 1);
      (v_5 : expression (bv 1)) <- eval (extract v_3 1 2);
      (v_6 : expression (bv 1)) <- eval (extract v_3 2 3);
      (v_7 : expression (bv 1)) <- eval (extract v_3 3 4);
      (v_8 : expression (bv 1)) <- eval (extract v_3 4 5);
      (v_9 : expression (bv 1)) <- eval (extract v_3 5 6);
      (v_10 : expression (bv 1)) <- eval (extract v_3 6 7);
      (v_11 : expression (bv 1)) <- eval (extract v_3 7 8);
      (v_12 : expression (bv 1)) <- eval (extract v_3 8 9);
      (v_13 : expression (bv 1)) <- eval (extract v_3 9 10);
      (v_14 : expression (bv 1)) <- eval (extract v_3 10 11);
      (v_15 : expression (bv 1)) <- eval (extract v_3 11 12);
      (v_16 : expression (bv 1)) <- eval (extract v_3 12 13);
      (v_17 : expression (bv 1)) <- eval (extract v_3 13 14);
      (v_18 : expression (bv 1)) <- eval (extract v_3 14 15);
      (v_19 : expression (bv 1)) <- eval (extract v_3 15 16);
      setRegister (lhs.of_reg r16_1) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_4) (concat (expression.bv_nat 1 0) v_5))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_6) (concat (expression.bv_nat 1 0) v_7))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_8) (concat (expression.bv_nat 1 0) v_9))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_10) (concat (expression.bv_nat 1 0) v_11))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_12) (concat (expression.bv_nat 1 0) v_13))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_14) (concat (expression.bv_nat 1 0) v_15))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_16) (concat (expression.bv_nat 1 0) v_17))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_18) (concat (expression.bv_nat 1 0) v_19))))))));
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
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 1 2);
      (v_5 : expression (bv 1)) <- eval (extract v_2 2 3);
      (v_6 : expression (bv 1)) <- eval (extract v_2 3 4);
      (v_7 : expression (bv 1)) <- eval (extract v_2 4 5);
      (v_8 : expression (bv 1)) <- eval (extract v_2 5 6);
      (v_9 : expression (bv 1)) <- eval (extract v_2 6 7);
      (v_10 : expression (bv 1)) <- eval (extract v_2 7 8);
      (v_11 : expression (bv 1)) <- eval (extract v_2 8 9);
      (v_12 : expression (bv 1)) <- eval (extract v_2 9 10);
      (v_13 : expression (bv 1)) <- eval (extract v_2 10 11);
      (v_14 : expression (bv 1)) <- eval (extract v_2 11 12);
      (v_15 : expression (bv 1)) <- eval (extract v_2 12 13);
      (v_16 : expression (bv 1)) <- eval (extract v_2 13 14);
      (v_17 : expression (bv 1)) <- eval (extract v_2 14 15);
      (v_18 : expression (bv 1)) <- eval (extract v_2 15 16);
      setRegister (lhs.of_reg r16_1) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_5) (concat (expression.bv_nat 1 0) v_6))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_7) (concat (expression.bv_nat 1 0) v_8))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_9) (concat (expression.bv_nat 1 0) v_10))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_11) (concat (expression.bv_nat 1 0) v_12))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_13) (concat (expression.bv_nat 1 0) v_14))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_15) (concat (expression.bv_nat 1 0) v_16))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) v_17) (concat (expression.bv_nat 1 0) v_18))))))));
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end
