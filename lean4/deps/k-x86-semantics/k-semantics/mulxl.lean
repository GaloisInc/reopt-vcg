def mulxl1 : instruction :=
  definst "mulxl" $ do
    pattern fun (v_2789 : reg (bv 32)) (v_2790 : reg (bv 32)) (v_2791 : reg (bv 32)) => do
      v_4302 <- getRegister rdx;
      v_4305 <- getRegister v_2789;
      v_4307 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_4302 32 64)) (concat (expression.bv_nat 32 0) v_4305));
      setRegister (lhs.of_reg v_2790) (extract v_4307 32 64);
      setRegister (lhs.of_reg v_2791) (extract v_4307 0 32);
      pure ()
    pat_end;
    pattern fun (v_2778 : Mem) (v_2779 : reg (bv 32)) (v_2780 : reg (bv 32)) => do
      v_9070 <- evaluateAddress v_2778;
      v_9073 <- load v_9070 4;
      v_9075 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_9070 32 64)) (concat (expression.bv_nat 32 0) v_9073));
      setRegister (lhs.of_reg v_2780) (extract v_9075 0 32);
      setRegister (lhs.of_reg v_2779) (extract v_9075 32 64);
      pure ()
    pat_end
