def vcvtph2ps : instruction :=
  definst "vcvtph2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      v_4 <- eval (bv_bitcast_to_fp(extract v_3 0 16));
      v_5 <- eval (bv_bitcast_to_fp(extract v_3 16 32));
      v_6 <- eval (bv_bitcast_to_fp(extract v_3 32 48));
      v_7 <- eval (bv_bitcast_to_fp(extract v_3 48 64));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) (fp_bitcast_to_bv (fp_round v_7 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (bv_bitcast_to_fp(extract v_3 0 16));
      v_5 <- eval (bv_bitcast_to_fp(extract v_3 16 32));
      v_6 <- eval (bv_bitcast_to_fp(extract v_3 32 48));
      v_7 <- eval (bv_bitcast_to_fp(extract v_3 48 64));
      v_8 <- eval (bv_bitcast_to_fp(extract v_3 64 80));
      v_9 <- eval (bv_bitcast_to_fp(extract v_3 80 96));
      v_10 <- eval (bv_bitcast_to_fp(extract v_3 96 112));
      v_11 <- eval (bv_bitcast_to_fp(extract v_3 112 128));
      setRegister (lhs.of_reg ymm_1) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_8 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_10 24 8) 32) (fp_bitcast_to_bv (fp_round v_11 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- eval (bv_bitcast_to_fp(extract v_2 64 80));
      v_4 <- eval (bv_bitcast_to_fp(extract v_2 80 96));
      v_5 <- eval (bv_bitcast_to_fp(extract v_2 96 112));
      v_6 <- eval (bv_bitcast_to_fp(extract v_2 112 128));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_round v_3 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (fp_bitcast_to_bv (fp_round v_6 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- eval (bv_bitcast_to_fp(extract v_2 0 16));
      v_4 <- eval (bv_bitcast_to_fp(extract v_2 16 32));
      v_5 <- eval (bv_bitcast_to_fp(extract v_2 32 48));
      v_6 <- eval (bv_bitcast_to_fp(extract v_2 48 64));
      v_7 <- eval (bv_bitcast_to_fp(extract v_2 64 80));
      v_8 <- eval (bv_bitcast_to_fp(extract v_2 80 96));
      v_9 <- eval (bv_bitcast_to_fp(extract v_2 96 112));
      v_10 <- eval (bv_bitcast_to_fp(extract v_2 112 128));
      setRegister (lhs.of_reg ymm_1) (concat (fp_bitcast_to_bv (fp_round v_3 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_8 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) (fp_bitcast_to_bv (fp_round v_10 24 8) 32))))))));
      pure ()
    pat_end
