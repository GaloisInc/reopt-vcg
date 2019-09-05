def psignb1 : instruction :=
  definst "psignb" $ do
    pattern fun (v_2995 : reg (bv 128)) (v_2996 : reg (bv 128)) => do
      v_7265 <- getRegister v_2995;
      v_7266 <- eval (extract v_7265 0 8);
      v_7268 <- getRegister v_2996;
      v_7269 <- eval (extract v_7268 0 8);
      v_7275 <- eval (extract v_7265 8 16);
      v_7277 <- eval (extract v_7268 8 16);
      v_7283 <- eval (extract v_7265 16 24);
      v_7285 <- eval (extract v_7268 16 24);
      v_7291 <- eval (extract v_7265 24 32);
      v_7293 <- eval (extract v_7268 24 32);
      v_7299 <- eval (extract v_7265 32 40);
      v_7301 <- eval (extract v_7268 32 40);
      v_7307 <- eval (extract v_7265 40 48);
      v_7309 <- eval (extract v_7268 40 48);
      v_7315 <- eval (extract v_7265 48 56);
      v_7317 <- eval (extract v_7268 48 56);
      v_7323 <- eval (extract v_7265 56 64);
      v_7325 <- eval (extract v_7268 56 64);
      v_7331 <- eval (extract v_7265 64 72);
      v_7333 <- eval (extract v_7268 64 72);
      v_7339 <- eval (extract v_7265 72 80);
      v_7341 <- eval (extract v_7268 72 80);
      v_7347 <- eval (extract v_7265 80 88);
      v_7349 <- eval (extract v_7268 80 88);
      v_7355 <- eval (extract v_7265 88 96);
      v_7357 <- eval (extract v_7268 88 96);
      v_7363 <- eval (extract v_7265 96 104);
      v_7365 <- eval (extract v_7268 96 104);
      v_7371 <- eval (extract v_7265 104 112);
      v_7373 <- eval (extract v_7268 104 112);
      v_7379 <- eval (extract v_7265 112 120);
      v_7381 <- eval (extract v_7268 112 120);
      v_7387 <- eval (extract v_7265 120 128);
      v_7389 <- eval (extract v_7268 120 128);
      setRegister (lhs.of_reg v_2996) (concat (mux (sgt v_7266 (expression.bv_nat 8 0)) v_7269 (mux (eq v_7266 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7269 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7275 (expression.bv_nat 8 0)) v_7277 (mux (eq v_7275 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7277 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7283 (expression.bv_nat 8 0)) v_7285 (mux (eq v_7283 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7285 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7291 (expression.bv_nat 8 0)) v_7293 (mux (eq v_7291 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7293 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7299 (expression.bv_nat 8 0)) v_7301 (mux (eq v_7299 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7301 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7307 (expression.bv_nat 8 0)) v_7309 (mux (eq v_7307 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7309 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7315 (expression.bv_nat 8 0)) v_7317 (mux (eq v_7315 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7317 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7323 (expression.bv_nat 8 0)) v_7325 (mux (eq v_7323 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7325 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7331 (expression.bv_nat 8 0)) v_7333 (mux (eq v_7331 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7333 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7339 (expression.bv_nat 8 0)) v_7341 (mux (eq v_7339 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7341 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7347 (expression.bv_nat 8 0)) v_7349 (mux (eq v_7347 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7349 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7355 (expression.bv_nat 8 0)) v_7357 (mux (eq v_7355 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7357 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7363 (expression.bv_nat 8 0)) v_7365 (mux (eq v_7363 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7365 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7371 (expression.bv_nat 8 0)) v_7373 (mux (eq v_7371 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7373 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7379 (expression.bv_nat 8 0)) v_7381 (mux (eq v_7379 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7381 (expression.bv_nat 8 255))))) (mux (sgt v_7387 (expression.bv_nat 8 0)) v_7389 (mux (eq v_7387 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7389 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2992 : Mem) (v_2991 : reg (bv 128)) => do
      v_13978 <- evaluateAddress v_2992;
      v_13979 <- load v_13978 16;
      v_13980 <- eval (extract v_13979 0 8);
      v_13982 <- getRegister v_2991;
      v_13983 <- eval (extract v_13982 0 8);
      v_13989 <- eval (extract v_13979 8 16);
      v_13991 <- eval (extract v_13982 8 16);
      v_13997 <- eval (extract v_13979 16 24);
      v_13999 <- eval (extract v_13982 16 24);
      v_14005 <- eval (extract v_13979 24 32);
      v_14007 <- eval (extract v_13982 24 32);
      v_14013 <- eval (extract v_13979 32 40);
      v_14015 <- eval (extract v_13982 32 40);
      v_14021 <- eval (extract v_13979 40 48);
      v_14023 <- eval (extract v_13982 40 48);
      v_14029 <- eval (extract v_13979 48 56);
      v_14031 <- eval (extract v_13982 48 56);
      v_14037 <- eval (extract v_13979 56 64);
      v_14039 <- eval (extract v_13982 56 64);
      v_14045 <- eval (extract v_13979 64 72);
      v_14047 <- eval (extract v_13982 64 72);
      v_14053 <- eval (extract v_13979 72 80);
      v_14055 <- eval (extract v_13982 72 80);
      v_14061 <- eval (extract v_13979 80 88);
      v_14063 <- eval (extract v_13982 80 88);
      v_14069 <- eval (extract v_13979 88 96);
      v_14071 <- eval (extract v_13982 88 96);
      v_14077 <- eval (extract v_13979 96 104);
      v_14079 <- eval (extract v_13982 96 104);
      v_14085 <- eval (extract v_13979 104 112);
      v_14087 <- eval (extract v_13982 104 112);
      v_14093 <- eval (extract v_13979 112 120);
      v_14095 <- eval (extract v_13982 112 120);
      v_14101 <- eval (extract v_13979 120 128);
      v_14103 <- eval (extract v_13982 120 128);
      setRegister (lhs.of_reg v_2991) (concat (mux (sgt v_13980 (expression.bv_nat 8 0)) v_13983 (mux (eq v_13980 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13983 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13989 (expression.bv_nat 8 0)) v_13991 (mux (eq v_13989 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13991 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13997 (expression.bv_nat 8 0)) v_13999 (mux (eq v_13997 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13999 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14005 (expression.bv_nat 8 0)) v_14007 (mux (eq v_14005 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14007 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14013 (expression.bv_nat 8 0)) v_14015 (mux (eq v_14013 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14015 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14021 (expression.bv_nat 8 0)) v_14023 (mux (eq v_14021 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14023 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14029 (expression.bv_nat 8 0)) v_14031 (mux (eq v_14029 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14031 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14037 (expression.bv_nat 8 0)) v_14039 (mux (eq v_14037 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14039 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14045 (expression.bv_nat 8 0)) v_14047 (mux (eq v_14045 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14047 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14053 (expression.bv_nat 8 0)) v_14055 (mux (eq v_14053 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14055 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14061 (expression.bv_nat 8 0)) v_14063 (mux (eq v_14061 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14063 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14069 (expression.bv_nat 8 0)) v_14071 (mux (eq v_14069 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14071 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14077 (expression.bv_nat 8 0)) v_14079 (mux (eq v_14077 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14079 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14085 (expression.bv_nat 8 0)) v_14087 (mux (eq v_14085 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14087 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14093 (expression.bv_nat 8 0)) v_14095 (mux (eq v_14093 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14095 (expression.bv_nat 8 255))))) (mux (sgt v_14101 (expression.bv_nat 8 0)) v_14103 (mux (eq v_14101 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14103 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end
