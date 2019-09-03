def popcntw1 : instruction :=
  definst "popcntw" $ do
    pattern fun (v_2870 : reg (bv 16)) (v_2871 : reg (bv 16)) => do
      v_6331 <- getRegister v_2870;
      setRegister (lhs.of_reg v_2871) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 0 1)) (concat (expression.bv_nat 1 0) (extract v_6331 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 2 3)) (concat (expression.bv_nat 1 0) (extract v_6331 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 4 5)) (concat (expression.bv_nat 1 0) (extract v_6331 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 6 7)) (concat (expression.bv_nat 1 0) (extract v_6331 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 8 9)) (concat (expression.bv_nat 1 0) (extract v_6331 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 10 11)) (concat (expression.bv_nat 1 0) (extract v_6331 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 12 13)) (concat (expression.bv_nat 1 0) (extract v_6331 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_6331 14 15)) (concat (expression.bv_nat 1 0) (extract v_6331 15 16)))))))));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister zf (zeroFlag v_6331);
      setRegister af (expression.bv_nat 1 0);
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2865 : Mem) (v_2866 : reg (bv 16)) => do
      v_13241 <- evaluateAddress v_2865;
      v_13242 <- load v_13241 2;
      setRegister (lhs.of_reg v_2866) (add (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 0 1)) (concat (expression.bv_nat 1 0) (extract v_13242 1 2)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 2 3)) (concat (expression.bv_nat 1 0) (extract v_13242 3 4)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 4 5)) (concat (expression.bv_nat 1 0) (extract v_13242 5 6)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 6 7)) (concat (expression.bv_nat 1 0) (extract v_13242 7 8)))))))) (concat (expression.bv_nat 8 0) (add (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 8 9)) (concat (expression.bv_nat 1 0) (extract v_13242 9 10)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 10 11)) (concat (expression.bv_nat 1 0) (extract v_13242 11 12)))))) (concat (expression.bv_nat 4 0) (add (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 12 13)) (concat (expression.bv_nat 1 0) (extract v_13242 13 14)))) (concat (expression.bv_nat 2 0) (add (concat (expression.bv_nat 1 0) (extract v_13242 14 15)) (concat (expression.bv_nat 1 0) (extract v_13242 15 16)))))))));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag v_13242);
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
