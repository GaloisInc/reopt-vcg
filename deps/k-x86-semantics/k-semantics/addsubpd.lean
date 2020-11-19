def addsubpd : instruction :=
  definst "addsubpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 v_3);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      (v_9 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      (v_11 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_add v_4 v_8) 64) (fp_bitcast_to_bv (fp_sub v_10 v_12) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 v_3);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      (v_8 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_add v_4 v_7) 64) (fp_bitcast_to_bv (fp_sub v_9 v_11) 64));
      pure ()
    pat_end
