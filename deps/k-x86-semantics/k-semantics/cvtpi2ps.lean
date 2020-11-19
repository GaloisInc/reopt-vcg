def cvtpi2ps : instruction :=
  definst "cvtpi2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_5 32 64);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 24 8) 32) (fp_bitcast_to_bv (Int2Float (svalueMInt v_7) 24 8) 32)));
      pure ()
    pat_end
