def salb1 : instruction :=
  definst "salb" $ do
    pattern fun cl (v_2891 : reg (bv 8)) => do
      v_5887 <- getRegister rcx;
      v_5889 <- eval (bv_and (extract v_5887 56 64) (expression.bv_nat 8 31));
      v_5890 <- eval (uge v_5889 (expression.bv_nat 8 8));
      v_5893 <- eval (eq v_5889 (expression.bv_nat 8 0));
      v_5894 <- eval (notBool_ v_5893);
      v_5895 <- getRegister v_2891;
      v_5900 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5895) (uvalueMInt (concat (expression.bv_nat 1 0) v_5889))) 0 9);
      v_5904 <- getRegister cf;
      v_5909 <- eval (bit_or (bit_and v_5890 undef) (bit_and (notBool_ v_5890) (bit_or (bit_and v_5894 (eq (extract v_5900 0 1) (expression.bv_nat 1 1))) (bit_and v_5893 (eq v_5904 (expression.bv_nat 1 1))))));
      v_5912 <- eval (eq (extract v_5900 1 2) (expression.bv_nat 1 1));
      v_5914 <- getRegister sf;
      v_5919 <- eval (extract v_5900 1 9);
      v_5922 <- getRegister zf;
      v_5927 <- eval (bit_and v_5894 undef);
      v_5928 <- getRegister af;
      v_5961 <- getRegister pf;
      v_5966 <- eval (eq v_5889 (expression.bv_nat 8 1));
      v_5971 <- getRegister of;
      setRegister (lhs.of_reg v_2891) v_5919;
      setRegister of (mux (bit_or (bit_and v_5966 (notBool_ (eq v_5909 v_5912))) (bit_and (notBool_ v_5966) (bit_or v_5927 (bit_and v_5893 (eq v_5971 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5894 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5900 8 9) (expression.bv_nat 1 1)) (eq (extract v_5900 7 8) (expression.bv_nat 1 1)))) (eq (extract v_5900 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5900 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5900 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5900 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5900 2 3) (expression.bv_nat 1 1)))) v_5912)) (bit_and v_5893 (eq v_5961 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5927 (bit_and v_5893 (eq v_5928 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5894 (eq v_5919 (expression.bv_nat 8 0))) (bit_and v_5893 (eq v_5922 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5894 v_5912) (bit_and v_5893 (eq v_5914 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5909 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2894 : imm int) (v_2896 : reg (bv 8)) => do
      v_5986 <- eval (bv_and (handleImmediateWithSignExtend v_2894 8 8) (expression.bv_nat 8 31));
      v_5987 <- eval (uge v_5986 (expression.bv_nat 8 8));
      v_5990 <- eval (eq v_5986 (expression.bv_nat 8 0));
      v_5991 <- eval (notBool_ v_5990);
      v_5992 <- getRegister v_2896;
      v_5997 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5992) (uvalueMInt (concat (expression.bv_nat 1 0) v_5986))) 0 9);
      v_6001 <- getRegister cf;
      v_6006 <- eval (bit_or (bit_and v_5987 undef) (bit_and (notBool_ v_5987) (bit_or (bit_and v_5991 (eq (extract v_5997 0 1) (expression.bv_nat 1 1))) (bit_and v_5990 (eq v_6001 (expression.bv_nat 1 1))))));
      v_6009 <- eval (eq (extract v_5997 1 2) (expression.bv_nat 1 1));
      v_6011 <- getRegister sf;
      v_6016 <- eval (extract v_5997 1 9);
      v_6019 <- getRegister zf;
      v_6024 <- eval (bit_and v_5991 undef);
      v_6025 <- getRegister af;
      v_6058 <- getRegister pf;
      v_6063 <- eval (eq v_5986 (expression.bv_nat 8 1));
      v_6068 <- getRegister of;
      setRegister (lhs.of_reg v_2896) v_6016;
      setRegister of (mux (bit_or (bit_and v_6063 (notBool_ (eq v_6006 v_6009))) (bit_and (notBool_ v_6063) (bit_or v_6024 (bit_and v_5990 (eq v_6068 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5991 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5997 8 9) (expression.bv_nat 1 1)) (eq (extract v_5997 7 8) (expression.bv_nat 1 1)))) (eq (extract v_5997 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5997 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5997 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5997 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5997 2 3) (expression.bv_nat 1 1)))) v_6009)) (bit_and v_5990 (eq v_6058 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6024 (bit_and v_5990 (eq v_6025 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5991 (eq v_6016 (expression.bv_nat 8 0))) (bit_and v_5990 (eq v_6019 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5991 v_6009) (bit_and v_5990 (eq v_6011 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6006 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2903 : reg (bv 8)) => do
      v_6084 <- getRegister v_2903;
      v_6087 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6084) 1) 0 9);
      v_6088 <- eval (extract v_6087 0 1);
      v_6089 <- eval (extract v_6087 1 2);
      v_6090 <- eval (extract v_6087 1 9);
      setRegister (lhs.of_reg v_2903) v_6090;
      setRegister of (mux (notBool_ (eq (eq v_6088 (expression.bv_nat 1 1)) (eq v_6089 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6090);
      setRegister af undef;
      setRegister zf (zeroFlag v_6090);
      setRegister sf v_6089;
      setRegister cf v_6088;
      pure ()
    pat_end;
    pattern fun (v_2899 : reg (bv 8)) => do
      v_9312 <- getRegister v_2899;
      v_9315 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9312) 1) 0 9);
      v_9317 <- eval (eq (extract v_9315 0 1) (expression.bv_nat 1 1));
      v_9320 <- eval (eq (extract v_9315 1 2) (expression.bv_nat 1 1));
      v_9322 <- eval (extract v_9315 1 9);
      setRegister (lhs.of_reg v_2899) v_9322;
      setRegister of (mux (notBool_ (eq v_9317 v_9320)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9322);
      setRegister zf (zeroFlag v_9322);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux v_9320 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9317 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2899 : reg (bv 8)) => do
      v_9335 <- getRegister v_2899;
      v_9338 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9335) 1) 0 9);
      v_9339 <- eval (extract v_9338 0 1);
      v_9340 <- eval (extract v_9338 1 2);
      v_9341 <- eval (extract v_9338 1 9);
      setRegister (lhs.of_reg v_2899) v_9341;
      setRegister of (mux (notBool_ (eq (eq v_9339 (expression.bv_nat 1 1)) (eq v_9340 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9341);
      setRegister zf (zeroFlag v_9341);
      setRegister af undef;
      setRegister sf v_9340;
      setRegister cf v_9339;
      pure ()
    pat_end;
    pattern fun (v_2915 : reg (bv 8)) => do
      v_9356 <- getRegister v_2915;
      v_9359 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9356) 1) 0 9);
      v_9361 <- eval (eq (extract v_9359 0 1) (expression.bv_nat 1 1));
      v_9364 <- eval (eq (extract v_9359 1 2) (expression.bv_nat 1 1));
      v_9366 <- eval (extract v_9359 1 9);
      setRegister (lhs.of_reg v_2915) v_9366;
      setRegister of (mux (notBool_ (eq v_9361 v_9364)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9366);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9366);
      setRegister sf (mux v_9364 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9361 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2915 : reg (bv 8)) => do
      v_9379 <- getRegister v_2915;
      v_9382 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9379) 1) 0 9);
      v_9383 <- eval (extract v_9382 0 1);
      v_9384 <- eval (extract v_9382 1 2);
      v_9385 <- eval (extract v_9382 1 9);
      setRegister (lhs.of_reg v_2915) v_9385;
      setRegister of (mux (notBool_ (eq (eq v_9383 (expression.bv_nat 1 1)) (eq v_9384 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9385);
      setRegister af undef;
      setRegister zf (zeroFlag v_9385);
      setRegister sf v_9384;
      setRegister cf v_9383;
      pure ()
    pat_end;
    pattern fun cl (v_2877 : Mem) => do
      v_15227 <- evaluateAddress v_2877;
      v_15228 <- load v_15227 1;
      v_15230 <- getRegister rcx;
      v_15232 <- eval (bv_and (extract v_15230 56 64) (expression.bv_nat 8 31));
      v_15236 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_15228) (uvalueMInt (concat (expression.bv_nat 1 0) v_15232))) 0 9);
      v_15237 <- eval (extract v_15236 1 9);
      store v_15227 v_15237 1;
      v_15239 <- eval (uge v_15232 (expression.bv_nat 8 8));
      v_15242 <- eval (eq v_15232 (expression.bv_nat 8 0));
      v_15243 <- eval (notBool_ v_15242);
      v_15247 <- getRegister cf;
      v_15252 <- eval (bit_or (bit_and v_15239 undef) (bit_and (notBool_ v_15239) (bit_or (bit_and v_15243 (eq (extract v_15236 0 1) (expression.bv_nat 1 1))) (bit_and v_15242 (eq v_15247 (expression.bv_nat 1 1))))));
      v_15255 <- eval (eq (extract v_15236 1 2) (expression.bv_nat 1 1));
      v_15257 <- getRegister sf;
      v_15264 <- getRegister zf;
      v_15269 <- eval (bit_and v_15243 undef);
      v_15270 <- getRegister af;
      v_15303 <- getRegister pf;
      v_15308 <- eval (eq v_15232 (expression.bv_nat 8 1));
      v_15313 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15308 (notBool_ (eq v_15252 v_15255))) (bit_and (notBool_ v_15308) (bit_or v_15269 (bit_and v_15242 (eq v_15313 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15243 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15236 8 9) (expression.bv_nat 1 1)) (eq (extract v_15236 7 8) (expression.bv_nat 1 1)))) (eq (extract v_15236 6 7) (expression.bv_nat 1 1)))) (eq (extract v_15236 5 6) (expression.bv_nat 1 1)))) (eq (extract v_15236 4 5) (expression.bv_nat 1 1)))) (eq (extract v_15236 3 4) (expression.bv_nat 1 1)))) (eq (extract v_15236 2 3) (expression.bv_nat 1 1)))) v_15255)) (bit_and v_15242 (eq v_15303 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15269 (bit_and v_15242 (eq v_15270 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15243 (eq v_15237 (expression.bv_nat 8 0))) (bit_and v_15242 (eq v_15264 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15243 v_15255) (bit_and v_15242 (eq v_15257 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15252 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2881 : imm int) (v_2880 : Mem) => do
      v_15326 <- evaluateAddress v_2880;
      v_15327 <- load v_15326 1;
      v_15330 <- eval (bv_and (handleImmediateWithSignExtend v_2881 8 8) (expression.bv_nat 8 31));
      v_15334 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_15327) (uvalueMInt (concat (expression.bv_nat 1 0) v_15330))) 0 9);
      v_15335 <- eval (extract v_15334 1 9);
      store v_15326 v_15335 1;
      v_15337 <- eval (uge v_15330 (expression.bv_nat 8 8));
      v_15340 <- eval (eq v_15330 (expression.bv_nat 8 0));
      v_15341 <- eval (notBool_ v_15340);
      v_15345 <- getRegister cf;
      v_15350 <- eval (bit_or (bit_and v_15337 undef) (bit_and (notBool_ v_15337) (bit_or (bit_and v_15341 (eq (extract v_15334 0 1) (expression.bv_nat 1 1))) (bit_and v_15340 (eq v_15345 (expression.bv_nat 1 1))))));
      v_15353 <- eval (eq (extract v_15334 1 2) (expression.bv_nat 1 1));
      v_15355 <- getRegister sf;
      v_15362 <- getRegister zf;
      v_15367 <- eval (bit_and v_15341 undef);
      v_15368 <- getRegister af;
      v_15401 <- getRegister pf;
      v_15406 <- eval (eq v_15330 (expression.bv_nat 8 1));
      v_15411 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15406 (notBool_ (eq v_15350 v_15353))) (bit_and (notBool_ v_15406) (bit_or v_15367 (bit_and v_15340 (eq v_15411 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15341 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15334 8 9) (expression.bv_nat 1 1)) (eq (extract v_15334 7 8) (expression.bv_nat 1 1)))) (eq (extract v_15334 6 7) (expression.bv_nat 1 1)))) (eq (extract v_15334 5 6) (expression.bv_nat 1 1)))) (eq (extract v_15334 4 5) (expression.bv_nat 1 1)))) (eq (extract v_15334 3 4) (expression.bv_nat 1 1)))) (eq (extract v_15334 2 3) (expression.bv_nat 1 1)))) v_15353)) (bit_and v_15340 (eq v_15401 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15367 (bit_and v_15340 (eq v_15368 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15341 (eq v_15335 (expression.bv_nat 8 0))) (bit_and v_15340 (eq v_15362 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15341 v_15353) (bit_and v_15340 (eq v_15355 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15350 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2884 : Mem) => do
      v_17921 <- evaluateAddress v_2884;
      v_17922 <- load v_17921 1;
      v_17925 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_17922) 1) 0 9);
      v_17926 <- eval (extract v_17925 1 9);
      store v_17921 v_17926 1;
      v_17929 <- eval (eq (extract v_17925 0 1) (expression.bv_nat 1 1));
      v_17932 <- eval (eq (extract v_17925 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_17929 v_17932)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_17926);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_17926);
      setRegister sf (mux v_17932 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_17929 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2884 : Mem) => do
      v_17945 <- evaluateAddress v_2884;
      v_17946 <- load v_17945 1;
      v_17949 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_17946) 1) 0 9);
      v_17950 <- eval (extract v_17949 1 9);
      store v_17945 v_17950 1;
      v_17952 <- eval (extract v_17949 0 1);
      v_17953 <- eval (extract v_17949 1 2);
      setRegister of (mux (notBool_ (eq (eq v_17952 (expression.bv_nat 1 1)) (eq v_17953 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_17950);
      setRegister af undef;
      setRegister zf (zeroFlag v_17950);
      setRegister sf v_17953;
      setRegister cf v_17952;
      pure ()
    pat_end
