def shrq1 : instruction :=
  definst "shrq" $ do
    pattern fun cl (v_2956 : reg (bv 64)) => do
      v_6166 <- getRegister rcx;
      v_6168 <- eval (bv_and (extract v_6166 56 64) (expression.bv_nat 8 63));
      v_6169 <- eval (uge v_6168 (expression.bv_nat 8 64));
      v_6172 <- eval (eq v_6168 (expression.bv_nat 8 0));
      v_6173 <- eval (notBool_ v_6172);
      v_6174 <- getRegister v_2956;
      v_6178 <- eval (lshr (concat v_6174 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_6168)));
      v_6182 <- getRegister cf;
      v_6192 <- getRegister sf;
      v_6197 <- eval (bit_and v_6173 undef);
      v_6198 <- getRegister af;
      v_6203 <- eval (extract v_6178 0 64);
      v_6206 <- getRegister zf;
      v_6241 <- getRegister pf;
      v_6246 <- eval (eq v_6168 (expression.bv_nat 8 1));
      v_6251 <- getRegister of;
      setRegister (lhs.of_reg v_2956) v_6203;
      setRegister of (mux (bit_or (bit_and v_6246 (eq (extract v_6174 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6246) (bit_or v_6197 (bit_and v_6172 (eq v_6251 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6173 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6178 63 64) (expression.bv_nat 1 1)) (eq (extract v_6178 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6178 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6178 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6178 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6178 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6178 57 58) (expression.bv_nat 1 1)))) (eq (extract v_6178 56 57) (expression.bv_nat 1 1)))) (bit_and v_6172 (eq v_6241 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6173 (eq v_6203 (expression.bv_nat 64 0))) (bit_and v_6172 (eq v_6206 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6197 (bit_and v_6172 (eq v_6198 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6173 (eq (extract v_6178 0 1) (expression.bv_nat 1 1))) (bit_and v_6172 (eq v_6192 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6169 undef) (bit_and (notBool_ v_6169) (bit_or (bit_and v_6173 (eq (extract v_6178 64 65) (expression.bv_nat 1 1))) (bit_and v_6172 (eq v_6182 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2960 : imm int) (v_2961 : reg (bv 64)) => do
      v_6266 <- eval (bv_and (handleImmediateWithSignExtend v_2960 8 8) (expression.bv_nat 8 63));
      v_6267 <- eval (uge v_6266 (expression.bv_nat 8 64));
      v_6270 <- eval (eq v_6266 (expression.bv_nat 8 0));
      v_6271 <- eval (notBool_ v_6270);
      v_6272 <- getRegister v_2961;
      v_6276 <- eval (lshr (concat v_6272 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_6266)));
      v_6280 <- getRegister cf;
      v_6290 <- getRegister sf;
      v_6295 <- eval (bit_and v_6271 undef);
      v_6296 <- getRegister af;
      v_6301 <- eval (extract v_6276 0 64);
      v_6304 <- getRegister zf;
      v_6339 <- getRegister pf;
      v_6344 <- eval (eq v_6266 (expression.bv_nat 8 1));
      v_6349 <- getRegister of;
      setRegister (lhs.of_reg v_2961) v_6301;
      setRegister of (mux (bit_or (bit_and v_6344 (eq (extract v_6272 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6344) (bit_or v_6295 (bit_and v_6270 (eq v_6349 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6271 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6276 63 64) (expression.bv_nat 1 1)) (eq (extract v_6276 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6276 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6276 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6276 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6276 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6276 57 58) (expression.bv_nat 1 1)))) (eq (extract v_6276 56 57) (expression.bv_nat 1 1)))) (bit_and v_6270 (eq v_6339 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6271 (eq v_6301 (expression.bv_nat 64 0))) (bit_and v_6270 (eq v_6304 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6295 (bit_and v_6270 (eq v_6296 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6271 (eq (extract v_6276 0 1) (expression.bv_nat 1 1))) (bit_and v_6270 (eq v_6290 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6267 undef) (bit_and (notBool_ v_6267) (bit_or (bit_and v_6271 (eq (extract v_6276 64 65) (expression.bv_nat 1 1))) (bit_and v_6270 (eq v_6280 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2968 : reg (bv 64)) => do
      v_6365 <- getRegister v_2968;
      v_6367 <- eval (lshr (concat v_6365 (expression.bv_nat 1 0)) 1);
      v_6370 <- eval (extract v_6367 0 64);
      setRegister (lhs.of_reg v_2968) v_6370;
      setRegister of (extract v_6365 0 1);
      setRegister pf (parityFlag (extract v_6367 56 64));
      setRegister zf (zeroFlag v_6370);
      setRegister af undef;
      setRegister sf (extract v_6367 0 1);
      setRegister cf (extract v_6367 64 65);
      pure ()
    pat_end;
    pattern fun (v_2965 : reg (bv 64)) => do
      v_8070 <- getRegister v_2965;
      v_8072 <- eval (lshr (concat v_8070 (expression.bv_nat 1 0)) 1);
      v_8079 <- eval (extract v_8072 0 64);
      setRegister (lhs.of_reg v_2965) v_8079;
      setRegister of (mux (eq (extract v_8070 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8072 56 64));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_8079);
      setRegister sf (mux (eq (extract v_8072 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_8072 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2965 : reg (bv 64)) => do
      v_8093 <- getRegister v_2965;
      v_8095 <- eval (lshr (concat v_8093 (expression.bv_nat 1 0)) 1);
      v_8098 <- eval (extract v_8095 0 64);
      setRegister (lhs.of_reg v_2965) v_8098;
      setRegister of (extract v_8093 0 1);
      setRegister pf (parityFlag (extract v_8095 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_8098);
      setRegister sf (extract v_8095 0 1);
      setRegister cf (extract v_8095 64 65);
      pure ()
    pat_end;
    pattern fun cl (v_2943 : Mem) => do
      v_12433 <- evaluateAddress v_2943;
      v_12434 <- load v_12433 8;
      v_12436 <- getRegister rcx;
      v_12438 <- eval (bv_and (extract v_12436 56 64) (expression.bv_nat 8 63));
      v_12441 <- eval (lshr (concat v_12434 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_12438)));
      v_12442 <- eval (extract v_12441 0 64);
      store v_12433 v_12442 8;
      v_12444 <- eval (uge v_12438 (expression.bv_nat 8 64));
      v_12447 <- eval (eq v_12438 (expression.bv_nat 8 0));
      v_12448 <- eval (notBool_ v_12447);
      v_12452 <- getRegister cf;
      v_12462 <- getRegister sf;
      v_12469 <- getRegister zf;
      v_12474 <- eval (bit_and v_12448 undef);
      v_12475 <- getRegister af;
      v_12510 <- getRegister pf;
      v_12515 <- eval (eq v_12438 (expression.bv_nat 8 1));
      v_12520 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12515 (eq (extract v_12434 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12515) (bit_or v_12474 (bit_and v_12447 (eq v_12520 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12448 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12441 63 64) (expression.bv_nat 1 1)) (eq (extract v_12441 62 63) (expression.bv_nat 1 1)))) (eq (extract v_12441 61 62) (expression.bv_nat 1 1)))) (eq (extract v_12441 60 61) (expression.bv_nat 1 1)))) (eq (extract v_12441 59 60) (expression.bv_nat 1 1)))) (eq (extract v_12441 58 59) (expression.bv_nat 1 1)))) (eq (extract v_12441 57 58) (expression.bv_nat 1 1)))) (eq (extract v_12441 56 57) (expression.bv_nat 1 1)))) (bit_and v_12447 (eq v_12510 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12474 (bit_and v_12447 (eq v_12475 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12448 (eq v_12442 (expression.bv_nat 64 0))) (bit_and v_12447 (eq v_12469 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12448 (eq (extract v_12441 0 1) (expression.bv_nat 1 1))) (bit_and v_12447 (eq v_12462 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12444 undef) (bit_and (notBool_ v_12444) (bit_or (bit_and v_12448 (eq (extract v_12441 64 65) (expression.bv_nat 1 1))) (bit_and v_12447 (eq v_12452 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2946 : imm int) (v_2947 : Mem) => do
      v_12533 <- evaluateAddress v_2947;
      v_12534 <- load v_12533 8;
      v_12537 <- eval (bv_and (handleImmediateWithSignExtend v_2946 8 8) (expression.bv_nat 8 63));
      v_12540 <- eval (lshr (concat v_12534 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) v_12537)));
      v_12541 <- eval (extract v_12540 0 64);
      store v_12533 v_12541 8;
      v_12543 <- eval (uge v_12537 (expression.bv_nat 8 64));
      v_12546 <- eval (eq v_12537 (expression.bv_nat 8 0));
      v_12547 <- eval (notBool_ v_12546);
      v_12551 <- getRegister cf;
      v_12561 <- getRegister sf;
      v_12568 <- getRegister zf;
      v_12573 <- eval (bit_and v_12547 undef);
      v_12574 <- getRegister af;
      v_12609 <- getRegister pf;
      v_12614 <- eval (eq v_12537 (expression.bv_nat 8 1));
      v_12619 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12614 (eq (extract v_12534 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12614) (bit_or v_12573 (bit_and v_12546 (eq v_12619 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12547 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12540 63 64) (expression.bv_nat 1 1)) (eq (extract v_12540 62 63) (expression.bv_nat 1 1)))) (eq (extract v_12540 61 62) (expression.bv_nat 1 1)))) (eq (extract v_12540 60 61) (expression.bv_nat 1 1)))) (eq (extract v_12540 59 60) (expression.bv_nat 1 1)))) (eq (extract v_12540 58 59) (expression.bv_nat 1 1)))) (eq (extract v_12540 57 58) (expression.bv_nat 1 1)))) (eq (extract v_12540 56 57) (expression.bv_nat 1 1)))) (bit_and v_12546 (eq v_12609 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12573 (bit_and v_12546 (eq v_12574 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12547 (eq v_12541 (expression.bv_nat 64 0))) (bit_and v_12546 (eq v_12568 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12547 (eq (extract v_12540 0 1) (expression.bv_nat 1 1))) (bit_and v_12546 (eq v_12561 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12543 undef) (bit_and (notBool_ v_12543) (bit_or (bit_and v_12547 (eq (extract v_12540 64 65) (expression.bv_nat 1 1))) (bit_and v_12546 (eq v_12551 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2950 : Mem) => do
      v_13453 <- evaluateAddress v_2950;
      v_13454 <- load v_13453 8;
      v_13456 <- eval (lshr (concat v_13454 (expression.bv_nat 1 0)) 1);
      v_13457 <- eval (extract v_13456 0 64);
      store v_13453 v_13457 8;
      setRegister of (mux (eq (extract v_13454 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13456 56 64));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13457);
      setRegister sf (mux (eq (extract v_13456 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13456 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2950 : Mem) => do
      v_13477 <- evaluateAddress v_2950;
      v_13478 <- load v_13477 8;
      v_13480 <- eval (lshr (concat v_13478 (expression.bv_nat 1 0)) 1);
      v_13481 <- eval (extract v_13480 0 64);
      store v_13477 v_13481 8;
      setRegister of (extract v_13478 0 1);
      setRegister pf (parityFlag (extract v_13480 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_13481);
      setRegister sf (extract v_13480 0 1);
      setRegister cf (extract v_13480 64 65);
      pure ()
    pat_end
