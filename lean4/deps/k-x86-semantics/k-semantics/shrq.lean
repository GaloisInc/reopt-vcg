def shrq1 : instruction :=
  definst "shrq" $ do
    pattern fun cl (v_3008 : reg (bv 64)) => do
      v_5623 <- getRegister rcx;
      v_5625 <- eval (bv_and (extract v_5623 56 64) (expression.bv_nat 8 63));
      v_5626 <- eval (eq v_5625 (expression.bv_nat 8 0));
      v_5627 <- eval (notBool_ v_5626);
      v_5628 <- getRegister v_3008;
      v_5631 <- eval (lshr (concat v_5628 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_5625));
      v_5632 <- eval (extract v_5631 0 64);
      v_5635 <- getRegister zf;
      v_5641 <- getRegister sf;
      v_5648 <- getRegister pf;
      v_5652 <- eval (eq v_5625 (expression.bv_nat 8 1));
      v_5656 <- eval (bit_and v_5627 undef);
      v_5657 <- getRegister of;
      v_5663 <- eval (uge v_5625 (expression.bv_nat 8 64));
      v_5668 <- getRegister cf;
      v_5674 <- getRegister af;
      setRegister (lhs.of_reg v_3008) v_5632;
      setRegister af (bit_or v_5656 (bit_and v_5626 (eq v_5674 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5663 undef) (bit_and (notBool_ v_5663) (bit_or (bit_and v_5627 (isBitSet v_5631 64)) (bit_and v_5626 (eq v_5668 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5652 (isBitSet v_5628 0)) (bit_and (notBool_ v_5652) (bit_or v_5656 (bit_and v_5626 (eq v_5657 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5627 (parityFlag (extract v_5631 56 64))) (bit_and v_5626 (eq v_5648 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5627 (isBitSet v_5631 0)) (bit_and v_5626 (eq v_5641 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5627 (eq v_5632 (expression.bv_nat 64 0))) (bit_and v_5626 (eq v_5635 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3011 : imm int) (v_3013 : reg (bv 64)) => do
      v_5686 <- eval (bv_and (handleImmediateWithSignExtend v_3011 8 8) (expression.bv_nat 8 63));
      v_5687 <- eval (eq v_5686 (expression.bv_nat 8 0));
      v_5688 <- eval (notBool_ v_5687);
      v_5689 <- getRegister v_3013;
      v_5692 <- eval (lshr (concat v_5689 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_5686));
      v_5693 <- eval (extract v_5692 0 64);
      v_5696 <- getRegister zf;
      v_5702 <- getRegister sf;
      v_5709 <- getRegister pf;
      v_5713 <- eval (eq v_5686 (expression.bv_nat 8 1));
      v_5717 <- eval (bit_and v_5688 undef);
      v_5718 <- getRegister of;
      v_5724 <- eval (uge v_5686 (expression.bv_nat 8 64));
      v_5729 <- getRegister cf;
      v_5735 <- getRegister af;
      setRegister (lhs.of_reg v_3013) v_5693;
      setRegister af (bit_or v_5717 (bit_and v_5687 (eq v_5735 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5724 undef) (bit_and (notBool_ v_5724) (bit_or (bit_and v_5688 (isBitSet v_5692 64)) (bit_and v_5687 (eq v_5729 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5713 (isBitSet v_5689 0)) (bit_and (notBool_ v_5713) (bit_or v_5717 (bit_and v_5687 (eq v_5718 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5688 (parityFlag (extract v_5692 56 64))) (bit_and v_5687 (eq v_5709 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5688 (isBitSet v_5692 0)) (bit_and v_5687 (eq v_5702 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5688 (eq v_5693 (expression.bv_nat 64 0))) (bit_and v_5687 (eq v_5696 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3016 : reg (bv 64)) => do
      v_7141 <- getRegister v_3016;
      v_7143 <- eval (lshr (concat v_7141 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_7144 <- eval (extract v_7143 0 64);
      setRegister (lhs.of_reg v_3016) v_7144;
      setRegister af undef;
      setRegister cf (isBitSet v_7143 64);
      setRegister of (isBitSet v_7141 0);
      setRegister pf (parityFlag (extract v_7143 56 64));
      setRegister sf (isBitSet v_7143 0);
      setRegister zf (zeroFlag v_7144);
      pure ()
    pat_end;
    pattern fun cl (v_2994 : Mem) => do
      v_10438 <- evaluateAddress v_2994;
      v_10439 <- load v_10438 8;
      v_10441 <- getRegister rcx;
      v_10443 <- eval (bv_and (extract v_10441 56 64) (expression.bv_nat 8 63));
      v_10445 <- eval (lshr (concat v_10439 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_10443));
      v_10446 <- eval (extract v_10445 0 64);
      store v_10438 v_10446 8;
      v_10448 <- eval (eq v_10443 (expression.bv_nat 8 0));
      v_10449 <- eval (notBool_ v_10448);
      v_10452 <- getRegister zf;
      v_10458 <- getRegister sf;
      v_10465 <- getRegister pf;
      v_10469 <- eval (eq v_10443 (expression.bv_nat 8 1));
      v_10473 <- eval (bit_and v_10449 undef);
      v_10474 <- getRegister of;
      v_10480 <- eval (uge v_10443 (expression.bv_nat 8 64));
      v_10485 <- getRegister cf;
      v_10491 <- getRegister af;
      setRegister af (bit_or v_10473 (bit_and v_10448 (eq v_10491 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10480 undef) (bit_and (notBool_ v_10480) (bit_or (bit_and v_10449 (isBitSet v_10445 64)) (bit_and v_10448 (eq v_10485 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10469 (isBitSet v_10439 0)) (bit_and (notBool_ v_10469) (bit_or v_10473 (bit_and v_10448 (eq v_10474 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10449 (parityFlag (extract v_10445 56 64))) (bit_and v_10448 (eq v_10465 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10449 (isBitSet v_10445 0)) (bit_and v_10448 (eq v_10458 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10449 (eq v_10446 (expression.bv_nat 64 0))) (bit_and v_10448 (eq v_10452 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2998 : imm int) (v_2997 : Mem) => do
      v_10501 <- evaluateAddress v_2997;
      v_10502 <- load v_10501 8;
      v_10505 <- eval (bv_and (handleImmediateWithSignExtend v_2998 8 8) (expression.bv_nat 8 63));
      v_10507 <- eval (lshr (concat v_10502 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_10505));
      v_10508 <- eval (extract v_10507 0 64);
      store v_10501 v_10508 8;
      v_10510 <- eval (eq v_10505 (expression.bv_nat 8 0));
      v_10511 <- eval (notBool_ v_10510);
      v_10514 <- getRegister zf;
      v_10520 <- getRegister sf;
      v_10527 <- getRegister pf;
      v_10531 <- eval (eq v_10505 (expression.bv_nat 8 1));
      v_10535 <- eval (bit_and v_10511 undef);
      v_10536 <- getRegister of;
      v_10542 <- eval (uge v_10505 (expression.bv_nat 8 64));
      v_10547 <- getRegister cf;
      v_10553 <- getRegister af;
      setRegister af (bit_or v_10535 (bit_and v_10510 (eq v_10553 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10542 undef) (bit_and (notBool_ v_10542) (bit_or (bit_and v_10511 (isBitSet v_10507 64)) (bit_and v_10510 (eq v_10547 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10531 (isBitSet v_10502 0)) (bit_and (notBool_ v_10531) (bit_or v_10535 (bit_and v_10510 (eq v_10536 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10511 (parityFlag (extract v_10507 56 64))) (bit_and v_10510 (eq v_10527 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10511 (isBitSet v_10507 0)) (bit_and v_10510 (eq v_10520 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10511 (eq v_10508 (expression.bv_nat 64 0))) (bit_and v_10510 (eq v_10514 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3001 : Mem) => do
      v_11128 <- evaluateAddress v_3001;
      v_11129 <- load v_11128 8;
      v_11131 <- eval (lshr (concat v_11129 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_11132 <- eval (extract v_11131 0 64);
      store v_11128 v_11132 8;
      setRegister af undef;
      setRegister cf (isBitSet v_11131 64);
      setRegister of (isBitSet v_11129 0);
      setRegister pf (parityFlag (extract v_11131 56 64));
      setRegister sf (isBitSet v_11131 0);
      setRegister zf (zeroFlag v_11132);
      pure ()
    pat_end
