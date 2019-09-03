def vmovd1 : instruction :=
  definst "vmovd" $ do
    pattern fun (v_2734 : reg (bv 128)) (v_2736 : reg (bv 32)) => do
      v_5062 <- getRegister v_2734;
      setRegister (lhs.of_reg v_2736) (extract v_5062 96 128);
      pure ()
    pat_end;
    pattern fun (v_2745 : reg (bv 32)) (v_2743 : reg (bv 128)) => do
      v_5069 <- getRegister v_2745;
      setRegister (lhs.of_reg v_2743) (concat (expression.bv_nat 96 0) (concat (extract v_5069 0 8) (extract v_5069 8 32)));
      pure ()
    pat_end;
    pattern fun (v_2731 : reg (bv 128)) (v_2730 : Mem) => do
      v_9849 <- evaluateAddress v_2730;
      v_9850 <- getRegister v_2731;
      store v_9849 (extract v_9850 96 128) 4;
      pure ()
    pat_end;
    pattern fun (v_2739 : Mem) (v_2740 : reg (bv 128)) => do
      v_11079 <- evaluateAddress v_2739;
      v_11080 <- load v_11079 4;
      setRegister (lhs.of_reg v_2740) (concat (expression.bv_nat 96 0) (concat (extract v_11080 0 8) (extract v_11080 8 32)));
      pure ()
    pat_end
