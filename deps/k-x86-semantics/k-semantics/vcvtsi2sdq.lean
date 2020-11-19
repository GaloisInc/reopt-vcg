def vcvtsi2sdq : instruction :=
  definst "vcvtsi2sdq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 8;
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg r64_0);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 53 11) 64));
      pure ()
    pat_end
