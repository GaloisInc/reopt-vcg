def sall1 : instruction :=
  definst "sall" $ do
    pattern fun cl (v_2936 : reg (bv 32)) => do
      v_6341 <- getRegister rcx;
      v_6343 <- eval (bv_and (extract v_6341 56 64) (expression.bv_nat 8 31));
      v_6344 <- eval (uge v_6343 (expression.bv_nat 8 32));
      v_6347 <- eval (eq v_6343 (expression.bv_nat 8 0));
      v_6348 <- eval (notBool_ v_6347);
      v_6349 <- getRegister v_2936;
      v_6354 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6349) (uvalueMInt (concat (expression.bv_nat 25 0) v_6343))) 0 33);
      v_6358 <- getRegister cf;
      v_6363 <- eval (bit_or (bit_and v_6344 undef) (bit_and (notBool_ v_6344) (bit_or (bit_and v_6348 (eq (extract v_6354 0 1) (expression.bv_nat 1 1))) (bit_and v_6347 (eq v_6358 (expression.bv_nat 1 1))))));
      v_6366 <- eval (eq (extract v_6354 1 2) (expression.bv_nat 1 1));
      v_6368 <- getRegister sf;
      v_6373 <- eval (extract v_6354 1 33);
      v_6376 <- getRegister zf;
      v_6381 <- eval (bit_and v_6348 undef);
      v_6382 <- getRegister af;
      v_6417 <- getRegister pf;
      v_6422 <- eval (eq v_6343 (expression.bv_nat 8 1));
      v_6427 <- getRegister of;
      setRegister (lhs.of_reg v_2936) v_6373;
      setRegister of (mux (bit_or (bit_and v_6422 (notBool_ (eq v_6363 v_6366))) (bit_and (notBool_ v_6422) (bit_or v_6381 (bit_and v_6347 (eq v_6427 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6348 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6354 32 33) (expression.bv_nat 1 1)) (eq (extract v_6354 31 32) (expression.bv_nat 1 1)))) (eq (extract v_6354 30 31) (expression.bv_nat 1 1)))) (eq (extract v_6354 29 30) (expression.bv_nat 1 1)))) (eq (extract v_6354 28 29) (expression.bv_nat 1 1)))) (eq (extract v_6354 27 28) (expression.bv_nat 1 1)))) (eq (extract v_6354 26 27) (expression.bv_nat 1 1)))) (eq (extract v_6354 25 26) (expression.bv_nat 1 1)))) (bit_and v_6347 (eq v_6417 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6381 (bit_and v_6347 (eq v_6382 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6348 (eq v_6373 (expression.bv_nat 32 0))) (bit_and v_6347 (eq v_6376 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6348 v_6366) (bit_and v_6347 (eq v_6368 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6363 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2939 : imm int) (v_2941 : reg (bv 32)) => do
      v_6442 <- eval (bv_and (handleImmediateWithSignExtend v_2939 8 8) (expression.bv_nat 8 31));
      v_6443 <- eval (uge v_6442 (expression.bv_nat 8 32));
      v_6446 <- eval (eq v_6442 (expression.bv_nat 8 0));
      v_6447 <- eval (notBool_ v_6446);
      v_6448 <- getRegister v_2941;
      v_6453 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6448) (uvalueMInt (concat (expression.bv_nat 25 0) v_6442))) 0 33);
      v_6457 <- getRegister cf;
      v_6462 <- eval (bit_or (bit_and v_6443 undef) (bit_and (notBool_ v_6443) (bit_or (bit_and v_6447 (eq (extract v_6453 0 1) (expression.bv_nat 1 1))) (bit_and v_6446 (eq v_6457 (expression.bv_nat 1 1))))));
      v_6465 <- eval (eq (extract v_6453 1 2) (expression.bv_nat 1 1));
      v_6467 <- getRegister sf;
      v_6472 <- eval (extract v_6453 1 33);
      v_6475 <- getRegister zf;
      v_6480 <- eval (bit_and v_6447 undef);
      v_6481 <- getRegister af;
      v_6516 <- getRegister pf;
      v_6521 <- eval (eq v_6442 (expression.bv_nat 8 1));
      v_6526 <- getRegister of;
      setRegister (lhs.of_reg v_2941) v_6472;
      setRegister of (mux (bit_or (bit_and v_6521 (notBool_ (eq v_6462 v_6465))) (bit_and (notBool_ v_6521) (bit_or v_6480 (bit_and v_6446 (eq v_6526 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6447 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6453 32 33) (expression.bv_nat 1 1)) (eq (extract v_6453 31 32) (expression.bv_nat 1 1)))) (eq (extract v_6453 30 31) (expression.bv_nat 1 1)))) (eq (extract v_6453 29 30) (expression.bv_nat 1 1)))) (eq (extract v_6453 28 29) (expression.bv_nat 1 1)))) (eq (extract v_6453 27 28) (expression.bv_nat 1 1)))) (eq (extract v_6453 26 27) (expression.bv_nat 1 1)))) (eq (extract v_6453 25 26) (expression.bv_nat 1 1)))) (bit_and v_6446 (eq v_6516 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6480 (bit_and v_6446 (eq v_6481 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6447 (eq v_6472 (expression.bv_nat 32 0))) (bit_and v_6446 (eq v_6475 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6447 v_6465) (bit_and v_6446 (eq v_6467 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6462 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2948 : reg (bv 32)) => do
      v_6542 <- getRegister v_2948;
      v_6545 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6542) 1) 0 33);
      v_6546 <- eval (extract v_6545 0 1);
      v_6547 <- eval (extract v_6545 1 2);
      v_6548 <- eval (extract v_6545 1 33);
      setRegister (lhs.of_reg v_2948) v_6548;
      setRegister of (mux (notBool_ (eq (eq v_6546 (expression.bv_nat 1 1)) (eq v_6547 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_6545 25 33));
      setRegister af undef;
      setRegister zf (zeroFlag v_6548);
      setRegister sf v_6547;
      setRegister cf v_6546;
      pure ()
    pat_end;
    pattern fun (v_2944 : reg (bv 32)) => do
      v_9429 <- getRegister v_2944;
      v_9432 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9429) 1) 0 33);
      v_9434 <- eval (eq (extract v_9432 0 1) (expression.bv_nat 1 1));
      v_9437 <- eval (eq (extract v_9432 1 2) (expression.bv_nat 1 1));
      v_9439 <- eval (extract v_9432 1 33);
      setRegister (lhs.of_reg v_2944) v_9439;
      setRegister of (mux (notBool_ (eq v_9434 v_9437)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9432 25 33));
      setRegister zf (zeroFlag v_9439);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux v_9437 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9434 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2944 : reg (bv 32)) => do
      v_9453 <- getRegister v_2944;
      v_9456 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9453) 1) 0 33);
      v_9457 <- eval (extract v_9456 0 1);
      v_9458 <- eval (extract v_9456 1 2);
      v_9459 <- eval (extract v_9456 1 33);
      setRegister (lhs.of_reg v_2944) v_9459;
      setRegister of (mux (notBool_ (eq (eq v_9457 (expression.bv_nat 1 1)) (eq v_9458 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9456 25 33));
      setRegister zf (zeroFlag v_9459);
      setRegister af undef;
      setRegister sf v_9458;
      setRegister cf v_9457;
      pure ()
    pat_end;
    pattern fun cl (v_2922 : Mem) => do
      v_15518 <- evaluateAddress v_2922;
      v_15519 <- load v_15518 4;
      v_15521 <- getRegister rcx;
      v_15523 <- eval (bv_and (extract v_15521 56 64) (expression.bv_nat 8 31));
      v_15527 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_15519) (uvalueMInt (concat (expression.bv_nat 25 0) v_15523))) 0 33);
      v_15528 <- eval (extract v_15527 1 33);
      store v_15518 v_15528 4;
      v_15530 <- eval (uge v_15523 (expression.bv_nat 8 32));
      v_15533 <- eval (eq v_15523 (expression.bv_nat 8 0));
      v_15534 <- eval (notBool_ v_15533);
      v_15538 <- getRegister cf;
      v_15543 <- eval (bit_or (bit_and v_15530 undef) (bit_and (notBool_ v_15530) (bit_or (bit_and v_15534 (eq (extract v_15527 0 1) (expression.bv_nat 1 1))) (bit_and v_15533 (eq v_15538 (expression.bv_nat 1 1))))));
      v_15546 <- eval (eq (extract v_15527 1 2) (expression.bv_nat 1 1));
      v_15548 <- getRegister sf;
      v_15555 <- getRegister zf;
      v_15560 <- eval (bit_and v_15534 undef);
      v_15561 <- getRegister af;
      v_15596 <- getRegister pf;
      v_15601 <- eval (eq v_15523 (expression.bv_nat 8 1));
      v_15606 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15601 (notBool_ (eq v_15543 v_15546))) (bit_and (notBool_ v_15601) (bit_or v_15560 (bit_and v_15533 (eq v_15606 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15534 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15527 32 33) (expression.bv_nat 1 1)) (eq (extract v_15527 31 32) (expression.bv_nat 1 1)))) (eq (extract v_15527 30 31) (expression.bv_nat 1 1)))) (eq (extract v_15527 29 30) (expression.bv_nat 1 1)))) (eq (extract v_15527 28 29) (expression.bv_nat 1 1)))) (eq (extract v_15527 27 28) (expression.bv_nat 1 1)))) (eq (extract v_15527 26 27) (expression.bv_nat 1 1)))) (eq (extract v_15527 25 26) (expression.bv_nat 1 1)))) (bit_and v_15533 (eq v_15596 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15560 (bit_and v_15533 (eq v_15561 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15534 (eq v_15528 (expression.bv_nat 32 0))) (bit_and v_15533 (eq v_15555 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15534 v_15546) (bit_and v_15533 (eq v_15548 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15543 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2926 : imm int) (v_2925 : Mem) => do
      v_15619 <- evaluateAddress v_2925;
      v_15620 <- load v_15619 4;
      v_15623 <- eval (bv_and (handleImmediateWithSignExtend v_2926 8 8) (expression.bv_nat 8 31));
      v_15627 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_15620) (uvalueMInt (concat (expression.bv_nat 25 0) v_15623))) 0 33);
      v_15628 <- eval (extract v_15627 1 33);
      store v_15619 v_15628 4;
      v_15630 <- eval (uge v_15623 (expression.bv_nat 8 32));
      v_15633 <- eval (eq v_15623 (expression.bv_nat 8 0));
      v_15634 <- eval (notBool_ v_15633);
      v_15638 <- getRegister cf;
      v_15643 <- eval (bit_or (bit_and v_15630 undef) (bit_and (notBool_ v_15630) (bit_or (bit_and v_15634 (eq (extract v_15627 0 1) (expression.bv_nat 1 1))) (bit_and v_15633 (eq v_15638 (expression.bv_nat 1 1))))));
      v_15646 <- eval (eq (extract v_15627 1 2) (expression.bv_nat 1 1));
      v_15648 <- getRegister sf;
      v_15655 <- getRegister zf;
      v_15660 <- eval (bit_and v_15634 undef);
      v_15661 <- getRegister af;
      v_15696 <- getRegister pf;
      v_15701 <- eval (eq v_15623 (expression.bv_nat 8 1));
      v_15706 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15701 (notBool_ (eq v_15643 v_15646))) (bit_and (notBool_ v_15701) (bit_or v_15660 (bit_and v_15633 (eq v_15706 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15634 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15627 32 33) (expression.bv_nat 1 1)) (eq (extract v_15627 31 32) (expression.bv_nat 1 1)))) (eq (extract v_15627 30 31) (expression.bv_nat 1 1)))) (eq (extract v_15627 29 30) (expression.bv_nat 1 1)))) (eq (extract v_15627 28 29) (expression.bv_nat 1 1)))) (eq (extract v_15627 27 28) (expression.bv_nat 1 1)))) (eq (extract v_15627 26 27) (expression.bv_nat 1 1)))) (eq (extract v_15627 25 26) (expression.bv_nat 1 1)))) (bit_and v_15633 (eq v_15696 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15660 (bit_and v_15633 (eq v_15661 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15634 (eq v_15628 (expression.bv_nat 32 0))) (bit_and v_15633 (eq v_15655 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15634 v_15646) (bit_and v_15633 (eq v_15648 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15643 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2929 : Mem) => do
      v_17967 <- evaluateAddress v_2929;
      v_17968 <- load v_17967 4;
      v_17971 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_17968) 1) 0 33);
      v_17972 <- eval (extract v_17971 1 33);
      store v_17967 v_17972 4;
      v_17975 <- eval (eq (extract v_17971 0 1) (expression.bv_nat 1 1));
      v_17978 <- eval (eq (extract v_17971 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_17975 v_17978)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17971 25 33));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_17972);
      setRegister sf (mux v_17978 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_17975 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2929 : Mem) => do
      v_17992 <- evaluateAddress v_2929;
      v_17993 <- load v_17992 4;
      v_17996 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_17993) 1) 0 33);
      v_17997 <- eval (extract v_17996 1 33);
      store v_17992 v_17997 4;
      v_17999 <- eval (extract v_17996 0 1);
      v_18000 <- eval (extract v_17996 1 2);
      setRegister of (mux (notBool_ (eq (eq v_17999 (expression.bv_nat 1 1)) (eq v_18000 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17996 25 33));
      setRegister af undef;
      setRegister zf (zeroFlag v_17997);
      setRegister sf v_18000;
      setRegister cf v_17999;
      pure ()
    pat_end
