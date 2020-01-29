def cvtsi2ssq : instruction :=
  definst "cvtsi2ssq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      setRegister (lhs.of_reg xmm_1) (concat v_3 (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      v_4 <- getRegister (lhs.of_reg r64_0);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 24 8) 32));
      pure ()
    pat_end
