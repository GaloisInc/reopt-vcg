def shlq1 : instruction :=
  definst "shlq" $ do
    pattern fun cl (v_2791 : reg (bv 64)) => do
      v_4988 <- getRegister rcx;
      v_4990 <- eval (bv_and (extract v_4988 56 64) (expression.bv_nat 8 63));
      v_4991 <- eval (uge v_4990 (expression.bv_nat 8 64));
      v_4994 <- eval (eq v_4990 (expression.bv_nat 8 0));
      v_4995 <- eval (notBool_ v_4994);
      v_4996 <- getRegister v_2791;
      v_5001 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4996) (uvalueMInt (concat (expression.bv_nat 57 0) v_4990))) 0 65);
      v_5005 <- getRegister cf;
      v_5010 <- eval (bit_or (bit_and v_4991 undef) (bit_and (notBool_ v_4991) (bit_or (bit_and v_4995 (eq (extract v_5001 0 1) (expression.bv_nat 1 1))) (bit_and v_4994 (eq v_5005 (expression.bv_nat 1 1))))));
      v_5013 <- eval (eq (extract v_5001 1 2) (expression.bv_nat 1 1));
      v_5015 <- getRegister sf;
      v_5020 <- eval (bit_and v_4995 undef);
      v_5021 <- getRegister af;
      v_5026 <- eval (extract v_5001 1 65);
      v_5029 <- getRegister zf;
      v_5064 <- getRegister pf;
      v_5069 <- eval (eq v_4990 (expression.bv_nat 8 1));
      v_5074 <- getRegister of;
      setRegister (lhs.of_reg v_2791) v_5026;
      setRegister of (mux (bit_or (bit_and v_5069 (notBool_ (eq v_5010 v_5013))) (bit_and (notBool_ v_5069) (bit_or v_5020 (bit_and v_4994 (eq v_5074 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4995 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5001 64 65) (expression.bv_nat 1 1)) (eq (extract v_5001 63 64) (expression.bv_nat 1 1)))) (eq (extract v_5001 62 63) (expression.bv_nat 1 1)))) (eq (extract v_5001 61 62) (expression.bv_nat 1 1)))) (eq (extract v_5001 60 61) (expression.bv_nat 1 1)))) (eq (extract v_5001 59 60) (expression.bv_nat 1 1)))) (eq (extract v_5001 58 59) (expression.bv_nat 1 1)))) (eq (extract v_5001 57 58) (expression.bv_nat 1 1)))) (bit_and v_4994 (eq v_5064 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4995 (eq v_5026 (expression.bv_nat 64 0))) (bit_and v_4994 (eq v_5029 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5020 (bit_and v_4994 (eq v_5021 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4995 v_5013) (bit_and v_4994 (eq v_5015 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5010 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2795 : imm int) (v_2796 : reg (bv 64)) => do
      v_5089 <- eval (bv_and (handleImmediateWithSignExtend v_2795 8 8) (expression.bv_nat 8 63));
      v_5090 <- eval (uge v_5089 (expression.bv_nat 8 64));
      v_5093 <- eval (eq v_5089 (expression.bv_nat 8 0));
      v_5094 <- eval (notBool_ v_5093);
      v_5095 <- getRegister v_2796;
      v_5100 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5095) (uvalueMInt (concat (expression.bv_nat 57 0) v_5089))) 0 65);
      v_5104 <- getRegister cf;
      v_5109 <- eval (bit_or (bit_and v_5090 undef) (bit_and (notBool_ v_5090) (bit_or (bit_and v_5094 (eq (extract v_5100 0 1) (expression.bv_nat 1 1))) (bit_and v_5093 (eq v_5104 (expression.bv_nat 1 1))))));
      v_5112 <- eval (eq (extract v_5100 1 2) (expression.bv_nat 1 1));
      v_5114 <- getRegister sf;
      v_5119 <- eval (bit_and v_5094 undef);
      v_5120 <- getRegister af;
      v_5125 <- eval (extract v_5100 1 65);
      v_5128 <- getRegister zf;
      v_5163 <- getRegister pf;
      v_5168 <- eval (eq v_5089 (expression.bv_nat 8 1));
      v_5173 <- getRegister of;
      setRegister (lhs.of_reg v_2796) v_5125;
      setRegister of (mux (bit_or (bit_and v_5168 (notBool_ (eq v_5109 v_5112))) (bit_and (notBool_ v_5168) (bit_or v_5119 (bit_and v_5093 (eq v_5173 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5094 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5100 64 65) (expression.bv_nat 1 1)) (eq (extract v_5100 63 64) (expression.bv_nat 1 1)))) (eq (extract v_5100 62 63) (expression.bv_nat 1 1)))) (eq (extract v_5100 61 62) (expression.bv_nat 1 1)))) (eq (extract v_5100 60 61) (expression.bv_nat 1 1)))) (eq (extract v_5100 59 60) (expression.bv_nat 1 1)))) (eq (extract v_5100 58 59) (expression.bv_nat 1 1)))) (eq (extract v_5100 57 58) (expression.bv_nat 1 1)))) (bit_and v_5093 (eq v_5163 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5094 (eq v_5125 (expression.bv_nat 64 0))) (bit_and v_5093 (eq v_5128 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5119 (bit_and v_5093 (eq v_5120 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5094 v_5112) (bit_and v_5093 (eq v_5114 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_5109 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2800 : reg (bv 64)) => do
      v_5187 <- getRegister v_2800;
      v_5190 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5187) 1) 0 65);
      v_5191 <- eval (extract v_5190 0 1);
      v_5192 <- eval (extract v_5190 1 2);
      v_5193 <- eval (extract v_5190 1 65);
      setRegister (lhs.of_reg v_2800) v_5193;
      setRegister of (mux (notBool_ (eq (eq v_5191 (expression.bv_nat 1 1)) (eq v_5192 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_5190 57 65));
      setRegister zf (zeroFlag v_5193);
      setRegister af undef;
      setRegister sf v_5192;
      setRegister cf v_5191;
      pure ()
    pat_end;
    pattern fun cl (v_2781 : Mem) => do
      v_11261 <- evaluateAddress v_2781;
      v_11262 <- load v_11261 8;
      v_11264 <- getRegister rcx;
      v_11266 <- eval (bv_and (extract v_11264 56 64) (expression.bv_nat 8 63));
      v_11270 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11262) (uvalueMInt (concat (expression.bv_nat 57 0) v_11266))) 0 65);
      v_11271 <- eval (extract v_11270 1 65);
      store v_11261 v_11271 8;
      v_11273 <- eval (uge v_11266 (expression.bv_nat 8 64));
      v_11276 <- eval (eq v_11266 (expression.bv_nat 8 0));
      v_11277 <- eval (notBool_ v_11276);
      v_11281 <- getRegister cf;
      v_11286 <- eval (bit_or (bit_and v_11273 undef) (bit_and (notBool_ v_11273) (bit_or (bit_and v_11277 (eq (extract v_11270 0 1) (expression.bv_nat 1 1))) (bit_and v_11276 (eq v_11281 (expression.bv_nat 1 1))))));
      v_11289 <- eval (eq (extract v_11270 1 2) (expression.bv_nat 1 1));
      v_11291 <- getRegister sf;
      v_11298 <- getRegister zf;
      v_11303 <- eval (bit_and v_11277 undef);
      v_11304 <- getRegister af;
      v_11339 <- getRegister pf;
      v_11344 <- eval (eq v_11266 (expression.bv_nat 8 1));
      v_11349 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11344 (notBool_ (eq v_11286 v_11289))) (bit_and (notBool_ v_11344) (bit_or v_11303 (bit_and v_11276 (eq v_11349 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11277 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11270 64 65) (expression.bv_nat 1 1)) (eq (extract v_11270 63 64) (expression.bv_nat 1 1)))) (eq (extract v_11270 62 63) (expression.bv_nat 1 1)))) (eq (extract v_11270 61 62) (expression.bv_nat 1 1)))) (eq (extract v_11270 60 61) (expression.bv_nat 1 1)))) (eq (extract v_11270 59 60) (expression.bv_nat 1 1)))) (eq (extract v_11270 58 59) (expression.bv_nat 1 1)))) (eq (extract v_11270 57 58) (expression.bv_nat 1 1)))) (bit_and v_11276 (eq v_11339 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11303 (bit_and v_11276 (eq v_11304 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11277 (eq v_11271 (expression.bv_nat 64 0))) (bit_and v_11276 (eq v_11298 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11277 v_11289) (bit_and v_11276 (eq v_11291 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11286 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2784 : imm int) (v_2785 : Mem) => do
      v_11362 <- evaluateAddress v_2785;
      v_11363 <- load v_11362 8;
      v_11366 <- eval (bv_and (handleImmediateWithSignExtend v_2784 8 8) (expression.bv_nat 8 63));
      v_11370 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11363) (uvalueMInt (concat (expression.bv_nat 57 0) v_11366))) 0 65);
      v_11371 <- eval (extract v_11370 1 65);
      store v_11362 v_11371 8;
      v_11373 <- eval (uge v_11366 (expression.bv_nat 8 64));
      v_11376 <- eval (eq v_11366 (expression.bv_nat 8 0));
      v_11377 <- eval (notBool_ v_11376);
      v_11381 <- getRegister cf;
      v_11386 <- eval (bit_or (bit_and v_11373 undef) (bit_and (notBool_ v_11373) (bit_or (bit_and v_11377 (eq (extract v_11370 0 1) (expression.bv_nat 1 1))) (bit_and v_11376 (eq v_11381 (expression.bv_nat 1 1))))));
      v_11389 <- eval (eq (extract v_11370 1 2) (expression.bv_nat 1 1));
      v_11391 <- getRegister sf;
      v_11398 <- getRegister zf;
      v_11403 <- eval (bit_and v_11377 undef);
      v_11404 <- getRegister af;
      v_11439 <- getRegister pf;
      v_11444 <- eval (eq v_11366 (expression.bv_nat 8 1));
      v_11449 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11444 (notBool_ (eq v_11386 v_11389))) (bit_and (notBool_ v_11444) (bit_or v_11403 (bit_and v_11376 (eq v_11449 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11377 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11370 64 65) (expression.bv_nat 1 1)) (eq (extract v_11370 63 64) (expression.bv_nat 1 1)))) (eq (extract v_11370 62 63) (expression.bv_nat 1 1)))) (eq (extract v_11370 61 62) (expression.bv_nat 1 1)))) (eq (extract v_11370 60 61) (expression.bv_nat 1 1)))) (eq (extract v_11370 59 60) (expression.bv_nat 1 1)))) (eq (extract v_11370 58 59) (expression.bv_nat 1 1)))) (eq (extract v_11370 57 58) (expression.bv_nat 1 1)))) (bit_and v_11376 (eq v_11439 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11403 (bit_and v_11376 (eq v_11404 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11377 (eq v_11371 (expression.bv_nat 64 0))) (bit_and v_11376 (eq v_11398 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11377 v_11389) (bit_and v_11376 (eq v_11391 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11386 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
