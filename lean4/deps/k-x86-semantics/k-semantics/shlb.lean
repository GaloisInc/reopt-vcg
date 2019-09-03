def shlb1 : instruction :=
  definst "shlb" $ do
    pattern fun cl (v_2733 : reg (bv 8)) => do
      v_4315 <- getRegister rcx;
      v_4317 <- eval (bv_and (extract v_4315 56 64) (expression.bv_nat 8 31));
      v_4318 <- eval (uge v_4317 (expression.bv_nat 8 8));
      v_4321 <- eval (eq v_4317 (expression.bv_nat 8 0));
      v_4322 <- eval (notBool_ v_4321);
      v_4323 <- getRegister v_2733;
      v_4328 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4323) (uvalueMInt (concat (expression.bv_nat 1 0) v_4317))) 0 9);
      v_4332 <- getRegister cf;
      v_4337 <- eval (bit_or (bit_and v_4318 undef) (bit_and (notBool_ v_4318) (bit_or (bit_and v_4322 (eq (extract v_4328 0 1) (expression.bv_nat 1 1))) (bit_and v_4321 (eq v_4332 (expression.bv_nat 1 1))))));
      v_4340 <- eval (eq (extract v_4328 1 2) (expression.bv_nat 1 1));
      v_4342 <- getRegister sf;
      v_4347 <- eval (bit_and v_4322 undef);
      v_4348 <- getRegister af;
      v_4353 <- eval (extract v_4328 1 9);
      v_4356 <- getRegister zf;
      v_4389 <- getRegister pf;
      v_4394 <- eval (eq v_4317 (expression.bv_nat 8 1));
      v_4399 <- getRegister of;
      setRegister (lhs.of_reg v_2733) v_4353;
      setRegister of (mux (bit_or (bit_and v_4394 (notBool_ (eq v_4337 v_4340))) (bit_and (notBool_ v_4394) (bit_or v_4347 (bit_and v_4321 (eq v_4399 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4322 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4328 8 9) (expression.bv_nat 1 1)) (eq (extract v_4328 7 8) (expression.bv_nat 1 1)))) (eq (extract v_4328 6 7) (expression.bv_nat 1 1)))) (eq (extract v_4328 5 6) (expression.bv_nat 1 1)))) (eq (extract v_4328 4 5) (expression.bv_nat 1 1)))) (eq (extract v_4328 3 4) (expression.bv_nat 1 1)))) (eq (extract v_4328 2 3) (expression.bv_nat 1 1)))) v_4340)) (bit_and v_4321 (eq v_4389 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4322 (eq v_4353 (expression.bv_nat 8 0))) (bit_and v_4321 (eq v_4356 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4347 (bit_and v_4321 (eq v_4348 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4322 v_4340) (bit_and v_4321 (eq v_4342 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4337 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2736 : imm int) (v_2738 : reg (bv 8)) => do
      v_4414 <- eval (bv_and (handleImmediateWithSignExtend v_2736 8 8) (expression.bv_nat 8 31));
      v_4415 <- eval (uge v_4414 (expression.bv_nat 8 8));
      v_4418 <- eval (eq v_4414 (expression.bv_nat 8 0));
      v_4419 <- eval (notBool_ v_4418);
      v_4420 <- getRegister v_2738;
      v_4425 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4420) (uvalueMInt (concat (expression.bv_nat 1 0) v_4414))) 0 9);
      v_4429 <- getRegister cf;
      v_4434 <- eval (bit_or (bit_and v_4415 undef) (bit_and (notBool_ v_4415) (bit_or (bit_and v_4419 (eq (extract v_4425 0 1) (expression.bv_nat 1 1))) (bit_and v_4418 (eq v_4429 (expression.bv_nat 1 1))))));
      v_4437 <- eval (eq (extract v_4425 1 2) (expression.bv_nat 1 1));
      v_4439 <- getRegister sf;
      v_4444 <- eval (bit_and v_4419 undef);
      v_4445 <- getRegister af;
      v_4450 <- eval (extract v_4425 1 9);
      v_4453 <- getRegister zf;
      v_4486 <- getRegister pf;
      v_4491 <- eval (eq v_4414 (expression.bv_nat 8 1));
      v_4496 <- getRegister of;
      setRegister (lhs.of_reg v_2738) v_4450;
      setRegister of (mux (bit_or (bit_and v_4491 (notBool_ (eq v_4434 v_4437))) (bit_and (notBool_ v_4491) (bit_or v_4444 (bit_and v_4418 (eq v_4496 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4419 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4425 8 9) (expression.bv_nat 1 1)) (eq (extract v_4425 7 8) (expression.bv_nat 1 1)))) (eq (extract v_4425 6 7) (expression.bv_nat 1 1)))) (eq (extract v_4425 5 6) (expression.bv_nat 1 1)))) (eq (extract v_4425 4 5) (expression.bv_nat 1 1)))) (eq (extract v_4425 3 4) (expression.bv_nat 1 1)))) (eq (extract v_4425 2 3) (expression.bv_nat 1 1)))) v_4437)) (bit_and v_4418 (eq v_4486 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4419 (eq v_4450 (expression.bv_nat 8 0))) (bit_and v_4418 (eq v_4453 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4444 (bit_and v_4418 (eq v_4445 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4419 v_4437) (bit_and v_4418 (eq v_4439 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4434 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2742 : reg (bv 8)) => do
      v_4510 <- getRegister v_2742;
      v_4513 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4510) 1) 0 9);
      v_4514 <- eval (extract v_4513 0 1);
      v_4515 <- eval (extract v_4513 1 2);
      v_4516 <- eval (extract v_4513 1 9);
      setRegister (lhs.of_reg v_2742) v_4516;
      setRegister of (mux (notBool_ (eq (eq v_4514 (expression.bv_nat 1 1)) (eq v_4515 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4516);
      setRegister zf (zeroFlag v_4516);
      setRegister af undef;
      setRegister sf v_4515;
      setRegister cf v_4514;
      pure ()
    pat_end;
    pattern fun cl (v_2722 : Mem) => do
      v_10675 <- evaluateAddress v_2722;
      v_10676 <- load v_10675 1;
      v_10678 <- getRegister rcx;
      v_10680 <- eval (bv_and (extract v_10678 56 64) (expression.bv_nat 8 31));
      v_10684 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_10676) (uvalueMInt (concat (expression.bv_nat 1 0) v_10680))) 0 9);
      v_10685 <- eval (extract v_10684 1 9);
      store v_10675 v_10685 1;
      v_10687 <- eval (uge v_10680 (expression.bv_nat 8 8));
      v_10690 <- eval (eq v_10680 (expression.bv_nat 8 0));
      v_10691 <- eval (notBool_ v_10690);
      v_10695 <- getRegister cf;
      v_10700 <- eval (bit_or (bit_and v_10687 undef) (bit_and (notBool_ v_10687) (bit_or (bit_and v_10691 (eq (extract v_10684 0 1) (expression.bv_nat 1 1))) (bit_and v_10690 (eq v_10695 (expression.bv_nat 1 1))))));
      v_10703 <- eval (eq (extract v_10684 1 2) (expression.bv_nat 1 1));
      v_10705 <- getRegister sf;
      v_10712 <- getRegister zf;
      v_10717 <- eval (bit_and v_10691 undef);
      v_10718 <- getRegister af;
      v_10751 <- getRegister pf;
      v_10756 <- eval (eq v_10680 (expression.bv_nat 8 1));
      v_10761 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_10756 (notBool_ (eq v_10700 v_10703))) (bit_and (notBool_ v_10756) (bit_or v_10717 (bit_and v_10690 (eq v_10761 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_10691 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_10684 8 9) (expression.bv_nat 1 1)) (eq (extract v_10684 7 8) (expression.bv_nat 1 1)))) (eq (extract v_10684 6 7) (expression.bv_nat 1 1)))) (eq (extract v_10684 5 6) (expression.bv_nat 1 1)))) (eq (extract v_10684 4 5) (expression.bv_nat 1 1)))) (eq (extract v_10684 3 4) (expression.bv_nat 1 1)))) (eq (extract v_10684 2 3) (expression.bv_nat 1 1)))) v_10703)) (bit_and v_10690 (eq v_10751 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_10717 (bit_and v_10690 (eq v_10718 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_10691 (eq v_10685 (expression.bv_nat 8 0))) (bit_and v_10690 (eq v_10712 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_10691 v_10703) (bit_and v_10690 (eq v_10705 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_10700 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2725 : imm int) (v_2726 : Mem) => do
      v_10774 <- evaluateAddress v_2726;
      v_10775 <- load v_10774 1;
      v_10778 <- eval (bv_and (handleImmediateWithSignExtend v_2725 8 8) (expression.bv_nat 8 31));
      v_10782 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_10775) (uvalueMInt (concat (expression.bv_nat 1 0) v_10778))) 0 9);
      v_10783 <- eval (extract v_10782 1 9);
      store v_10774 v_10783 1;
      v_10785 <- eval (uge v_10778 (expression.bv_nat 8 8));
      v_10788 <- eval (eq v_10778 (expression.bv_nat 8 0));
      v_10789 <- eval (notBool_ v_10788);
      v_10793 <- getRegister cf;
      v_10798 <- eval (bit_or (bit_and v_10785 undef) (bit_and (notBool_ v_10785) (bit_or (bit_and v_10789 (eq (extract v_10782 0 1) (expression.bv_nat 1 1))) (bit_and v_10788 (eq v_10793 (expression.bv_nat 1 1))))));
      v_10801 <- eval (eq (extract v_10782 1 2) (expression.bv_nat 1 1));
      v_10803 <- getRegister sf;
      v_10810 <- getRegister zf;
      v_10815 <- eval (bit_and v_10789 undef);
      v_10816 <- getRegister af;
      v_10849 <- getRegister pf;
      v_10854 <- eval (eq v_10778 (expression.bv_nat 8 1));
      v_10859 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_10854 (notBool_ (eq v_10798 v_10801))) (bit_and (notBool_ v_10854) (bit_or v_10815 (bit_and v_10788 (eq v_10859 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_10789 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_10782 8 9) (expression.bv_nat 1 1)) (eq (extract v_10782 7 8) (expression.bv_nat 1 1)))) (eq (extract v_10782 6 7) (expression.bv_nat 1 1)))) (eq (extract v_10782 5 6) (expression.bv_nat 1 1)))) (eq (extract v_10782 4 5) (expression.bv_nat 1 1)))) (eq (extract v_10782 3 4) (expression.bv_nat 1 1)))) (eq (extract v_10782 2 3) (expression.bv_nat 1 1)))) v_10801)) (bit_and v_10788 (eq v_10849 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_10815 (bit_and v_10788 (eq v_10816 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_10789 (eq v_10783 (expression.bv_nat 8 0))) (bit_and v_10788 (eq v_10810 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_10789 v_10801) (bit_and v_10788 (eq v_10803 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_10798 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
