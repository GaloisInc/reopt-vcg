def haddps : instruction :=
  definst "haddps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      (v_6 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      v_12 <- getRegister (lhs.of_reg xmm_1);
      (v_13 : expression (bv 32)) <- eval (extract v_12 32 64);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      (v_15 : expression (bv 32)) <- eval (extract v_12 0 32);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      (v_17 : expression (bv 32)) <- eval (extract v_12 96 128);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      (v_19 : expression (bv 32)) <- eval (extract v_12 64 96);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat (fp_bitcast_to_bv (fp_add v_5 v_7) 32) (fp_bitcast_to_bv (fp_add v_9 v_11) 32)) (fp_bitcast_to_bv (fp_add v_14 v_16) 32)) (fp_bitcast_to_bv (fp_add v_18 v_20) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      (v_5 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      (v_7 : expression (bv 32)) <- eval (extract v_2 96 128);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      v_11 <- getRegister (lhs.of_reg xmm_1);
      (v_12 : expression (bv 32)) <- eval (extract v_11 32 64);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      (v_14 : expression (bv 32)) <- eval (extract v_11 0 32);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      (v_16 : expression (bv 32)) <- eval (extract v_11 96 128);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      (v_18 : expression (bv 32)) <- eval (extract v_11 64 96);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat (fp_bitcast_to_bv (fp_add v_4 v_6) 32) (fp_bitcast_to_bv (fp_add v_8 v_10) 32)) (fp_bitcast_to_bv (fp_add v_13 v_15) 32)) (fp_bitcast_to_bv (fp_add v_17 v_19) 32));
      pure ()
    pat_end
