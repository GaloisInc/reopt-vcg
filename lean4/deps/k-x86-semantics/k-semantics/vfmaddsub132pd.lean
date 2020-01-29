def vfmaddsub132pd : instruction :=
  definst "vfmaddsub132pd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 16;
      (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      (v_10 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      (v_12 : expression (bv 64)) <- eval (extract v_8 64 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      (v_14 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      setRegister (lhs.of_reg xmm_2) (concat (/- (_,_,_) -/ vfmadd132_double v_4 v_6 v_9) (fp_bitcast_to_bv (fp_sub (fp_mul v_11 v_13) v_15) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 32;
      (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      (v_10 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      (v_12 : expression (bv 64)) <- eval (extract v_8 64 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      (v_14 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      (v_16 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_17 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_18 : expression (bv 64)) <- eval (extract v_8 128 192);
      (v_19 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp64 v_19);
      (v_21 : expression (bv 64)) <- eval (extract v_8 192 256);
      v_22 <- eval (bv_bitcast_to_fp float_class.fp64 v_21);
      (v_23 : expression (bv 64)) <- eval (extract v_5 192 256);
      v_24 <- eval (bv_bitcast_to_fp float_class.fp64 v_23);
      setRegister (lhs.of_reg ymm_2) (concat (concat (/- (_,_,_) -/ vfmadd132_double v_4 v_6 v_9) (fp_bitcast_to_bv (fp_sub (fp_mul v_11 v_13) v_15) 64)) (concat (/- (_,_,_) -/ vfmadd132_double v_16 v_17 v_18) (fp_bitcast_to_bv (fp_sub (fp_mul v_20 v_22) v_24) 64)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- getRegister (lhs.of_reg xmm_0);
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      (v_11 : expression (bv 64)) <- eval (extract v_7 64 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      (v_13 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      setRegister (lhs.of_reg xmm_2) (concat (/- (_,_,_) -/ vfmadd132_double v_4 v_6 v_8) (fp_bitcast_to_bv (fp_sub (fp_mul v_10 v_12) v_14) 64));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- getRegister (lhs.of_reg ymm_0);
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      (v_11 : expression (bv 64)) <- eval (extract v_7 64 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      (v_13 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_16 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_17 : expression (bv 64)) <- eval (extract v_7 128 192);
      (v_18 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp64 v_18);
      (v_20 : expression (bv 64)) <- eval (extract v_7 192 256);
      v_21 <- eval (bv_bitcast_to_fp float_class.fp64 v_20);
      (v_22 : expression (bv 64)) <- eval (extract v_5 192 256);
      v_23 <- eval (bv_bitcast_to_fp float_class.fp64 v_22);
      setRegister (lhs.of_reg ymm_2) (concat (concat (/- (_,_,_) -/ vfmadd132_double v_4 v_6 v_8) (fp_bitcast_to_bv (fp_sub (fp_mul v_10 v_12) v_14) 64)) (concat (/- (_,_,_) -/ vfmadd132_double v_15 v_16 v_17) (fp_bitcast_to_bv (fp_sub (fp_mul v_19 v_21) v_23) 64)));
      pure ()
    pat_end
