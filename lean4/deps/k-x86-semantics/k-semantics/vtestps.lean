def vtestps1 : instruction :=
  definst "vtestps" $ do
    pattern fun (v_2446 : reg (bv 128)) (v_2447 : reg (bv 128)) => do
      v_3478 <- getRegister v_2447;
      v_3479 <- eval (extract v_3478 96 97);
      v_3483 <- getRegister v_2446;
      v_3484 <- eval (extract v_3483 96 97);
      v_3487 <- eval (extract v_3478 64 65);
      v_3491 <- eval (extract v_3483 64 65);
      v_3495 <- eval (extract v_3478 32 33);
      v_3499 <- eval (extract v_3483 32 33);
      v_3503 <- eval (extract v_3478 0 1);
      v_3507 <- eval (extract v_3483 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (bit_and (bit_and (eq (bv_and v_3479 v_3484) (expression.bv_nat 1 0)) (eq (bv_and v_3487 v_3491) (expression.bv_nat 1 0))) (eq (bv_and v_3495 v_3499) (expression.bv_nat 1 0))) (eq (bv_and v_3503 v_3507) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_3479 (mi (bitwidthMInt v_3479) -1)) v_3484) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_3487 (mi (bitwidthMInt v_3487) -1)) v_3491) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3495 (mi (bitwidthMInt v_3495) -1)) v_3499) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3503 (mi (bitwidthMInt v_3503) -1)) v_3507) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2454 : reg (bv 256)) (v_2455 : reg (bv 256)) => do
      v_3534 <- getRegister v_2455;
      v_3535 <- eval (extract v_3534 224 225);
      v_3539 <- getRegister v_2454;
      v_3540 <- eval (extract v_3539 224 225);
      v_3543 <- eval (extract v_3534 192 193);
      v_3547 <- eval (extract v_3539 192 193);
      v_3551 <- eval (extract v_3534 160 161);
      v_3555 <- eval (extract v_3539 160 161);
      v_3559 <- eval (extract v_3534 128 129);
      v_3563 <- eval (extract v_3539 128 129);
      v_3567 <- eval (extract v_3534 96 97);
      v_3571 <- eval (extract v_3539 96 97);
      v_3575 <- eval (extract v_3534 64 65);
      v_3579 <- eval (extract v_3539 64 65);
      v_3583 <- eval (extract v_3534 32 33);
      v_3587 <- eval (extract v_3539 32 33);
      v_3591 <- eval (extract v_3534 0 1);
      v_3595 <- eval (extract v_3539 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and v_3535 v_3540) (expression.bv_nat 1 0)) (eq (bv_and v_3543 v_3547) (expression.bv_nat 1 0))) (eq (bv_and v_3551 v_3555) (expression.bv_nat 1 0))) (eq (bv_and v_3559 v_3563) (expression.bv_nat 1 0))) (eq (bv_and v_3567 v_3571) (expression.bv_nat 1 0))) (eq (bv_and v_3575 v_3579) (expression.bv_nat 1 0))) (eq (bv_and v_3583 v_3587) (expression.bv_nat 1 0))) (eq (bv_and v_3591 v_3595) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_3535 (mi (bitwidthMInt v_3535) -1)) v_3540) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_3543 (mi (bitwidthMInt v_3543) -1)) v_3547) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3551 (mi (bitwidthMInt v_3551) -1)) v_3555) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3559 (mi (bitwidthMInt v_3559) -1)) v_3563) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3567 (mi (bitwidthMInt v_3567) -1)) v_3571) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3575 (mi (bitwidthMInt v_3575) -1)) v_3579) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3583 (mi (bitwidthMInt v_3583) -1)) v_3587) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_3591 (mi (bitwidthMInt v_3591) -1)) v_3595) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2440 : Mem) (v_2442 : reg (bv 128)) => do
      v_6744 <- getRegister v_2442;
      v_6745 <- eval (extract v_6744 96 97);
      v_6749 <- evaluateAddress v_2440;
      v_6750 <- load v_6749 16;
      v_6751 <- eval (extract v_6750 96 97);
      v_6754 <- eval (extract v_6744 64 65);
      v_6758 <- eval (extract v_6750 64 65);
      v_6762 <- eval (extract v_6744 32 33);
      v_6766 <- eval (extract v_6750 32 33);
      v_6770 <- eval (extract v_6744 0 1);
      v_6774 <- eval (extract v_6750 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (bit_and (bit_and (eq (bv_and v_6745 v_6751) (expression.bv_nat 1 0)) (eq (bv_and v_6754 v_6758) (expression.bv_nat 1 0))) (eq (bv_and v_6762 v_6766) (expression.bv_nat 1 0))) (eq (bv_and v_6770 v_6774) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_6745 (mi (bitwidthMInt v_6745) -1)) v_6751) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_6754 (mi (bitwidthMInt v_6754) -1)) v_6758) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6762 (mi (bitwidthMInt v_6762) -1)) v_6766) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6770 (mi (bitwidthMInt v_6770) -1)) v_6774) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2449 : Mem) (v_2450 : reg (bv 256)) => do
      v_6797 <- getRegister v_2450;
      v_6798 <- eval (extract v_6797 224 225);
      v_6802 <- evaluateAddress v_2449;
      v_6803 <- load v_6802 32;
      v_6804 <- eval (extract v_6803 224 225);
      v_6807 <- eval (extract v_6797 192 193);
      v_6811 <- eval (extract v_6803 192 193);
      v_6815 <- eval (extract v_6797 160 161);
      v_6819 <- eval (extract v_6803 160 161);
      v_6823 <- eval (extract v_6797 128 129);
      v_6827 <- eval (extract v_6803 128 129);
      v_6831 <- eval (extract v_6797 96 97);
      v_6835 <- eval (extract v_6803 96 97);
      v_6839 <- eval (extract v_6797 64 65);
      v_6843 <- eval (extract v_6803 64 65);
      v_6847 <- eval (extract v_6797 32 33);
      v_6851 <- eval (extract v_6803 32 33);
      v_6855 <- eval (extract v_6797 0 1);
      v_6859 <- eval (extract v_6803 0 1);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and v_6798 v_6804) (expression.bv_nat 1 0)) (eq (bv_and v_6807 v_6811) (expression.bv_nat 1 0))) (eq (bv_and v_6815 v_6819) (expression.bv_nat 1 0))) (eq (bv_and v_6823 v_6827) (expression.bv_nat 1 0))) (eq (bv_and v_6831 v_6835) (expression.bv_nat 1 0))) (eq (bv_and v_6839 v_6843) (expression.bv_nat 1 0))) (eq (bv_and v_6847 v_6851) (expression.bv_nat 1 0))) (eq (bv_and v_6855 v_6859) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (bit_and (eq (bv_and (bv_xor v_6798 (mi (bitwidthMInt v_6798) -1)) v_6804) (expression.bv_nat 1 0)) (eq (bv_and (bv_xor v_6807 (mi (bitwidthMInt v_6807) -1)) v_6811) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6815 (mi (bitwidthMInt v_6815) -1)) v_6819) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6823 (mi (bitwidthMInt v_6823) -1)) v_6827) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6831 (mi (bitwidthMInt v_6831) -1)) v_6835) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6839 (mi (bitwidthMInt v_6839) -1)) v_6843) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6847 (mi (bitwidthMInt v_6847) -1)) v_6851) (expression.bv_nat 1 0))) (eq (bv_and (bv_xor v_6855 (mi (bitwidthMInt v_6855) -1)) v_6859) (expression.bv_nat 1 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
