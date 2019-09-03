def shrq1 : instruction :=
  definst "shrq" $ do
    pattern fun cl (v_2944 : reg (bv 64)) => do
      v_6170 <- getRegister rcx;
      v_6172 <- eval (bv_and (extract v_6170 56 64) (expression.bv_nat 8 63));
      v_6173 <- eval (uge v_6172 (expression.bv_nat 8 64));
      v_6176 <- eval (eq v_6172 (expression.bv_nat 8 0));
      v_6177 <- eval (notBool_ v_6176);
      v_6178 <- getRegister v_2944;
      v_6182 <- eval (lshr (concat v_6178 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_6172)));
      v_6186 <- getRegister cf;
      v_6196 <- getRegister sf;
      v_6201 <- eval (extract v_6182 0 64);
      v_6204 <- getRegister zf;
      v_6209 <- eval (bit_and v_6177 undef);
      v_6210 <- getRegister af;
      v_6245 <- getRegister pf;
      v_6250 <- eval (eq v_6172 (expression.bv_nat 8 1));
      v_6255 <- getRegister of;
      setRegister (lhs.of_reg v_2944) v_6201;
      setRegister of (mux (bit_or (bit_and v_6250 (eq (extract v_6178 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6250) (bit_or v_6209 (bit_and v_6176 (eq v_6255 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6177 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6182 63 64) (expression.bv_nat 1 1)) (eq (extract v_6182 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6182 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6182 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6182 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6182 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6182 57 58) (expression.bv_nat 1 1)))) (eq (extract v_6182 56 57) (expression.bv_nat 1 1)))) (bit_and v_6176 (eq v_6245 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6209 (bit_and v_6176 (eq v_6210 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6177 (eq v_6201 (expression.bv_nat 64 0))) (bit_and v_6176 (eq v_6204 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6177 (eq (extract v_6182 0 1) (expression.bv_nat 1 1))) (bit_and v_6176 (eq v_6196 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6173 undef) (bit_and (notBool_ v_6173) (bit_or (bit_and v_6177 (eq (extract v_6182 64 65) (expression.bv_nat 1 1))) (bit_and v_6176 (eq v_6186 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2947 : imm int) (v_2949 : reg (bv 64)) => do
      v_6270 <- eval (bv_and (handleImmediateWithSignExtend v_2947 8 8) (expression.bv_nat 8 63));
      v_6271 <- eval (uge v_6270 (expression.bv_nat 8 64));
      v_6274 <- eval (eq v_6270 (expression.bv_nat 8 0));
      v_6275 <- eval (notBool_ v_6274);
      v_6276 <- getRegister v_2949;
      v_6280 <- eval (lshr (concat v_6276 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_6270)));
      v_6284 <- getRegister cf;
      v_6294 <- getRegister sf;
      v_6299 <- eval (extract v_6280 0 64);
      v_6302 <- getRegister zf;
      v_6307 <- eval (bit_and v_6275 undef);
      v_6308 <- getRegister af;
      v_6343 <- getRegister pf;
      v_6348 <- eval (eq v_6270 (expression.bv_nat 8 1));
      v_6353 <- getRegister of;
      setRegister (lhs.of_reg v_2949) v_6299;
      setRegister of (mux (bit_or (bit_and v_6348 (eq (extract v_6276 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6348) (bit_or v_6307 (bit_and v_6274 (eq v_6353 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6275 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6280 63 64) (expression.bv_nat 1 1)) (eq (extract v_6280 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6280 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6280 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6280 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6280 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6280 57 58) (expression.bv_nat 1 1)))) (eq (extract v_6280 56 57) (expression.bv_nat 1 1)))) (bit_and v_6274 (eq v_6343 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6307 (bit_and v_6274 (eq v_6308 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6275 (eq v_6299 (expression.bv_nat 64 0))) (bit_and v_6274 (eq v_6302 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6275 (eq (extract v_6280 0 1) (expression.bv_nat 1 1))) (bit_and v_6274 (eq v_6294 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6271 undef) (bit_and (notBool_ v_6271) (bit_or (bit_and v_6275 (eq (extract v_6280 64 65) (expression.bv_nat 1 1))) (bit_and v_6274 (eq v_6284 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2956 : reg (bv 64)) => do
      v_6369 <- getRegister v_2956;
      v_6371 <- eval (lshr (concat v_6369 (expression.bv_nat 1 0)) 1);
      v_6374 <- eval (extract v_6371 0 64);
      setRegister (lhs.of_reg v_2956) v_6374;
      setRegister of (extract v_6369 0 1);
      setRegister pf (parityFlag (extract v_6371 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_6374);
      setRegister sf (extract v_6371 0 1);
      setRegister cf (extract v_6371 64 65);
      pure ()
    pat_end;
    pattern fun (v_2952 : reg (bv 64)) => do
      v_8046 <- getRegister v_2952;
      v_8048 <- eval (lshr (concat v_8046 (expression.bv_nat 1 0)) 1);
      v_8055 <- eval (extract v_8048 0 64);
      setRegister (lhs.of_reg v_2952) v_8055;
      setRegister of (mux (eq (extract v_8046 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8048 56 64));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_8055);
      setRegister sf (mux (eq (extract v_8048 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_8048 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2952 : reg (bv 64)) => do
      v_8069 <- getRegister v_2952;
      v_8071 <- eval (lshr (concat v_8069 (expression.bv_nat 1 0)) 1);
      v_8074 <- eval (extract v_8071 0 64);
      setRegister (lhs.of_reg v_2952) v_8074;
      setRegister of (extract v_8069 0 1);
      setRegister pf (parityFlag (extract v_8071 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_8074);
      setRegister sf (extract v_8071 0 1);
      setRegister cf (extract v_8071 64 65);
      pure ()
    pat_end;
    pattern fun cl (v_2930 : Mem) => do
      v_12361 <- evaluateAddress v_2930;
      v_12362 <- load v_12361 8;
      v_12364 <- getRegister rcx;
      v_12366 <- eval (bv_and (extract v_12364 56 64) (expression.bv_nat 8 63));
      v_12369 <- eval (lshr (concat v_12362 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_12366)));
      v_12370 <- eval (extract v_12369 0 64);
      store v_12361 v_12370 8;
      v_12372 <- eval (uge v_12366 (expression.bv_nat 8 64));
      v_12375 <- eval (eq v_12366 (expression.bv_nat 8 0));
      v_12376 <- eval (notBool_ v_12375);
      v_12380 <- getRegister cf;
      v_12390 <- getRegister sf;
      v_12397 <- getRegister zf;
      v_12402 <- eval (bit_and v_12376 undef);
      v_12403 <- getRegister af;
      v_12438 <- getRegister pf;
      v_12443 <- eval (eq v_12366 (expression.bv_nat 8 1));
      v_12448 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12443 (eq (extract v_12362 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12443) (bit_or v_12402 (bit_and v_12375 (eq v_12448 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12376 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12369 63 64) (expression.bv_nat 1 1)) (eq (extract v_12369 62 63) (expression.bv_nat 1 1)))) (eq (extract v_12369 61 62) (expression.bv_nat 1 1)))) (eq (extract v_12369 60 61) (expression.bv_nat 1 1)))) (eq (extract v_12369 59 60) (expression.bv_nat 1 1)))) (eq (extract v_12369 58 59) (expression.bv_nat 1 1)))) (eq (extract v_12369 57 58) (expression.bv_nat 1 1)))) (eq (extract v_12369 56 57) (expression.bv_nat 1 1)))) (bit_and v_12375 (eq v_12438 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12402 (bit_and v_12375 (eq v_12403 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12376 (eq v_12370 (expression.bv_nat 64 0))) (bit_and v_12375 (eq v_12397 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12376 (eq (extract v_12369 0 1) (expression.bv_nat 1 1))) (bit_and v_12375 (eq v_12390 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12372 undef) (bit_and (notBool_ v_12372) (bit_or (bit_and v_12376 (eq (extract v_12369 64 65) (expression.bv_nat 1 1))) (bit_and v_12375 (eq v_12380 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2933 : imm int) (v_2934 : Mem) => do
      v_12461 <- evaluateAddress v_2934;
      v_12462 <- load v_12461 8;
      v_12465 <- eval (bv_and (handleImmediateWithSignExtend v_2933 8 8) (expression.bv_nat 8 63));
      v_12468 <- eval (lshr (concat v_12462 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_12465)));
      v_12469 <- eval (extract v_12468 0 64);
      store v_12461 v_12469 8;
      v_12471 <- eval (uge v_12465 (expression.bv_nat 8 64));
      v_12474 <- eval (eq v_12465 (expression.bv_nat 8 0));
      v_12475 <- eval (notBool_ v_12474);
      v_12479 <- getRegister cf;
      v_12489 <- getRegister sf;
      v_12496 <- getRegister zf;
      v_12501 <- eval (bit_and v_12475 undef);
      v_12502 <- getRegister af;
      v_12537 <- getRegister pf;
      v_12542 <- eval (eq v_12465 (expression.bv_nat 8 1));
      v_12547 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12542 (eq (extract v_12462 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12542) (bit_or v_12501 (bit_and v_12474 (eq v_12547 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12475 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12468 63 64) (expression.bv_nat 1 1)) (eq (extract v_12468 62 63) (expression.bv_nat 1 1)))) (eq (extract v_12468 61 62) (expression.bv_nat 1 1)))) (eq (extract v_12468 60 61) (expression.bv_nat 1 1)))) (eq (extract v_12468 59 60) (expression.bv_nat 1 1)))) (eq (extract v_12468 58 59) (expression.bv_nat 1 1)))) (eq (extract v_12468 57 58) (expression.bv_nat 1 1)))) (eq (extract v_12468 56 57) (expression.bv_nat 1 1)))) (bit_and v_12474 (eq v_12537 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12501 (bit_and v_12474 (eq v_12502 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12475 (eq v_12469 (expression.bv_nat 64 0))) (bit_and v_12474 (eq v_12496 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12475 (eq (extract v_12468 0 1) (expression.bv_nat 1 1))) (bit_and v_12474 (eq v_12489 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12471 undef) (bit_and (notBool_ v_12471) (bit_or (bit_and v_12475 (eq (extract v_12468 64 65) (expression.bv_nat 1 1))) (bit_and v_12474 (eq v_12479 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) => do
      v_13418 <- evaluateAddress v_2937;
      v_13419 <- load v_13418 8;
      v_13421 <- eval (lshr (concat v_13419 (expression.bv_nat 1 0)) 1);
      v_13422 <- eval (extract v_13421 0 64);
      store v_13418 v_13422 8;
      setRegister of (mux (eq (extract v_13419 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13421 56 64));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13422);
      setRegister sf (mux (eq (extract v_13421 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13421 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) => do
      v_13442 <- evaluateAddress v_2937;
      v_13443 <- load v_13442 8;
      v_13445 <- eval (lshr (concat v_13443 (expression.bv_nat 1 0)) 1);
      v_13446 <- eval (extract v_13445 0 64);
      store v_13442 v_13446 8;
      setRegister of (extract v_13443 0 1);
      setRegister pf (parityFlag (extract v_13445 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_13446);
      setRegister sf (extract v_13445 0 1);
      setRegister cf (extract v_13445 64 65);
      pure ()
    pat_end
