def salw1 : instruction :=
  definst "salw" $ do
    pattern fun cl (v_3044 : reg (bv 16)) => do
      v_6247 <- getRegister rcx;
      v_6249 <- eval (bv_and (extract v_6247 56 64) (expression.bv_nat 8 31));
      v_6250 <- eval (eq v_6249 (expression.bv_nat 8 0));
      v_6251 <- eval (notBool_ v_6250);
      v_6252 <- getRegister v_3044;
      v_6256 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6252) (concat (expression.bv_nat 9 0) v_6249)) 0 17);
      v_6257 <- eval (extract v_6256 1 17);
      v_6260 <- getRegister zf;
      v_6264 <- eval (isBitSet v_6256 1);
      v_6266 <- getRegister sf;
      v_6273 <- getRegister pf;
      v_6277 <- eval (eq v_6249 (expression.bv_nat 8 1));
      v_6278 <- eval (uge v_6249 (expression.bv_nat 8 16));
      v_6283 <- getRegister cf;
      v_6288 <- eval (bit_or (bit_and v_6278 undef) (bit_and (notBool_ v_6278) (bit_or (bit_and v_6251 (isBitSet v_6256 0)) (bit_and v_6250 (eq v_6283 (expression.bv_nat 1 1))))));
      v_6293 <- eval (bit_and v_6251 undef);
      v_6294 <- getRegister of;
      v_6300 <- getRegister af;
      setRegister (lhs.of_reg v_3044) v_6257;
      setRegister af (bit_or v_6293 (bit_and v_6250 (eq v_6300 (expression.bv_nat 1 1))));
      setRegister cf v_6288;
      setRegister of (bit_or (bit_and v_6277 (notBool_ (eq v_6288 v_6264))) (bit_and (notBool_ v_6277) (bit_or v_6293 (bit_and v_6250 (eq v_6294 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_6251 (parityFlag (extract v_6256 9 17))) (bit_and v_6250 (eq v_6273 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6251 v_6264) (bit_and v_6250 (eq v_6266 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6251 (eq v_6257 (expression.bv_nat 16 0))) (bit_and v_6250 (eq v_6260 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3051 : imm int) (v_3048 : reg (bv 16)) => do
      v_6312 <- eval (bv_and (handleImmediateWithSignExtend v_3051 8 8) (expression.bv_nat 8 31));
      v_6313 <- eval (eq v_6312 (expression.bv_nat 8 0));
      v_6314 <- eval (notBool_ v_6313);
      v_6315 <- getRegister v_3048;
      v_6319 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6315) (concat (expression.bv_nat 9 0) v_6312)) 0 17);
      v_6320 <- eval (extract v_6319 1 17);
      v_6323 <- getRegister zf;
      v_6327 <- eval (isBitSet v_6319 1);
      v_6329 <- getRegister sf;
      v_6336 <- getRegister pf;
      v_6340 <- eval (eq v_6312 (expression.bv_nat 8 1));
      v_6341 <- eval (uge v_6312 (expression.bv_nat 8 16));
      v_6346 <- getRegister cf;
      v_6351 <- eval (bit_or (bit_and v_6341 undef) (bit_and (notBool_ v_6341) (bit_or (bit_and v_6314 (isBitSet v_6319 0)) (bit_and v_6313 (eq v_6346 (expression.bv_nat 1 1))))));
      v_6356 <- eval (bit_and v_6314 undef);
      v_6357 <- getRegister of;
      v_6363 <- getRegister af;
      setRegister (lhs.of_reg v_3048) v_6320;
      setRegister af (bit_or v_6356 (bit_and v_6313 (eq v_6363 (expression.bv_nat 1 1))));
      setRegister cf v_6351;
      setRegister of (bit_or (bit_and v_6340 (notBool_ (eq v_6351 v_6327))) (bit_and (notBool_ v_6340) (bit_or v_6356 (bit_and v_6313 (eq v_6357 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_6314 (parityFlag (extract v_6319 9 17))) (bit_and v_6313 (eq v_6336 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6314 v_6327) (bit_and v_6313 (eq v_6329 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6314 (eq v_6320 (expression.bv_nat 16 0))) (bit_and v_6313 (eq v_6323 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3053 : reg (bv 16)) => do
      v_8361 <- getRegister v_3053;
      v_8364 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8361) (expression.bv_nat 17 1)) 0 17);
      v_8365 <- eval (extract v_8364 1 17);
      v_8367 <- eval (isBitSet v_8364 1);
      v_8370 <- eval (isBitSet v_8364 0);
      setRegister (lhs.of_reg v_3053) v_8365;
      setRegister af undef;
      setRegister cf v_8370;
      setRegister of (notBool_ (eq v_8370 v_8367));
      setRegister pf (parityFlag (extract v_8364 9 17));
      setRegister sf v_8367;
      setRegister zf (zeroFlag v_8365);
      pure ()
    pat_end;
    pattern fun cl (v_3033 : Mem) => do
      v_13385 <- evaluateAddress v_3033;
      v_13386 <- load v_13385 2;
      v_13388 <- getRegister rcx;
      v_13390 <- eval (bv_and (extract v_13388 56 64) (expression.bv_nat 8 31));
      v_13393 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13386) (concat (expression.bv_nat 9 0) v_13390)) 0 17);
      v_13394 <- eval (extract v_13393 1 17);
      store v_13385 v_13394 2;
      v_13396 <- eval (eq v_13390 (expression.bv_nat 8 0));
      v_13397 <- eval (notBool_ v_13396);
      v_13400 <- getRegister zf;
      v_13404 <- eval (isBitSet v_13393 1);
      v_13406 <- getRegister sf;
      v_13413 <- getRegister pf;
      v_13417 <- eval (eq v_13390 (expression.bv_nat 8 1));
      v_13418 <- eval (uge v_13390 (expression.bv_nat 8 16));
      v_13423 <- getRegister cf;
      v_13428 <- eval (bit_or (bit_and v_13418 undef) (bit_and (notBool_ v_13418) (bit_or (bit_and v_13397 (isBitSet v_13393 0)) (bit_and v_13396 (eq v_13423 (expression.bv_nat 1 1))))));
      v_13433 <- eval (bit_and v_13397 undef);
      v_13434 <- getRegister of;
      v_13440 <- getRegister af;
      setRegister af (bit_or v_13433 (bit_and v_13396 (eq v_13440 (expression.bv_nat 1 1))));
      setRegister cf v_13428;
      setRegister of (bit_or (bit_and v_13417 (notBool_ (eq v_13428 v_13404))) (bit_and (notBool_ v_13417) (bit_or v_13433 (bit_and v_13396 (eq v_13434 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_13397 (parityFlag (extract v_13393 9 17))) (bit_and v_13396 (eq v_13413 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13397 v_13404) (bit_and v_13396 (eq v_13406 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13397 (eq v_13394 (expression.bv_nat 16 0))) (bit_and v_13396 (eq v_13400 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3036 : imm int) (v_3037 : Mem) => do
      v_13450 <- evaluateAddress v_3037;
      v_13451 <- load v_13450 2;
      v_13454 <- eval (bv_and (handleImmediateWithSignExtend v_3036 8 8) (expression.bv_nat 8 31));
      v_13457 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13451) (concat (expression.bv_nat 9 0) v_13454)) 0 17);
      v_13458 <- eval (extract v_13457 1 17);
      store v_13450 v_13458 2;
      v_13460 <- eval (eq v_13454 (expression.bv_nat 8 0));
      v_13461 <- eval (notBool_ v_13460);
      v_13464 <- getRegister zf;
      v_13468 <- eval (isBitSet v_13457 1);
      v_13470 <- getRegister sf;
      v_13477 <- getRegister pf;
      v_13481 <- eval (eq v_13454 (expression.bv_nat 8 1));
      v_13482 <- eval (uge v_13454 (expression.bv_nat 8 16));
      v_13487 <- getRegister cf;
      v_13492 <- eval (bit_or (bit_and v_13482 undef) (bit_and (notBool_ v_13482) (bit_or (bit_and v_13461 (isBitSet v_13457 0)) (bit_and v_13460 (eq v_13487 (expression.bv_nat 1 1))))));
      v_13497 <- eval (bit_and v_13461 undef);
      v_13498 <- getRegister of;
      v_13504 <- getRegister af;
      setRegister af (bit_or v_13497 (bit_and v_13460 (eq v_13504 (expression.bv_nat 1 1))));
      setRegister cf v_13492;
      setRegister of (bit_or (bit_and v_13481 (notBool_ (eq v_13492 v_13468))) (bit_and (notBool_ v_13481) (bit_or v_13497 (bit_and v_13460 (eq v_13498 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_13461 (parityFlag (extract v_13457 9 17))) (bit_and v_13460 (eq v_13477 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13461 v_13468) (bit_and v_13460 (eq v_13470 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13461 (eq v_13458 (expression.bv_nat 16 0))) (bit_and v_13460 (eq v_13464 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3040 : Mem) => do
      v_14550 <- evaluateAddress v_3040;
      v_14551 <- load v_14550 2;
      v_14554 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_14551) (expression.bv_nat 17 1)) 0 17);
      v_14555 <- eval (extract v_14554 1 17);
      store v_14550 v_14555 2;
      v_14558 <- eval (isBitSet v_14554 1);
      v_14561 <- eval (isBitSet v_14554 0);
      setRegister af undef;
      setRegister cf v_14561;
      setRegister of (notBool_ (eq v_14561 v_14558));
      setRegister pf (parityFlag (extract v_14554 9 17));
      setRegister sf v_14558;
      setRegister zf (zeroFlag v_14555);
      pure ()
    pat_end
