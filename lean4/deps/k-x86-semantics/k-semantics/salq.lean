def salq1 : instruction :=
  definst "salq" $ do
    pattern fun cl (v_2954 : reg (bv 64)) => do
      v_6573 <- getRegister rcx;
      v_6575 <- eval (bv_and (extract v_6573 56 64) (expression.bv_nat 8 63));
      v_6576 <- eval (uge v_6575 (expression.bv_nat 8 64));
      v_6579 <- eval (eq v_6575 (expression.bv_nat 8 0));
      v_6580 <- eval (notBool_ v_6579);
      v_6581 <- getRegister v_2954;
      v_6582 <- eval (concat (expression.bv_nat 1 0) v_6581);
      v_6587 <- eval (extract (shl v_6582 (uvalueMInt (concat (expression.bv_nat 57 0) v_6575))) 0 (bitwidthMInt v_6582));
      v_6591 <- getRegister cf;
      v_6596 <- eval (bit_or (bit_and v_6576 undef) (bit_and (notBool_ v_6576) (bit_or (bit_and v_6580 (eq (extract v_6587 0 1) (expression.bv_nat 1 1))) (bit_and v_6579 (eq v_6591 (expression.bv_nat 1 1))))));
      v_6599 <- eval (eq (extract v_6587 1 2) (expression.bv_nat 1 1));
      v_6601 <- getRegister sf;
      v_6606 <- eval (bit_and v_6580 undef);
      v_6607 <- getRegister af;
      v_6612 <- eval (extract v_6587 1 65);
      v_6615 <- getRegister zf;
      v_6650 <- getRegister pf;
      v_6655 <- eval (eq v_6575 (expression.bv_nat 8 1));
      v_6660 <- getRegister of;
      setRegister (lhs.of_reg v_2954) v_6612;
      setRegister of (mux (bit_or (bit_and v_6655 (notBool_ (eq v_6596 v_6599))) (bit_and (notBool_ v_6655) (bit_or v_6606 (bit_and v_6579 (eq v_6660 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6580 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6587 64 65) (expression.bv_nat 1 1)) (eq (extract v_6587 63 64) (expression.bv_nat 1 1)))) (eq (extract v_6587 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6587 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6587 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6587 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6587 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6587 57 58) (expression.bv_nat 1 1)))) (bit_and v_6579 (eq v_6650 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6580 (eq v_6612 (expression.bv_nat 64 0))) (bit_and v_6579 (eq v_6615 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6606 (bit_and v_6579 (eq v_6607 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6580 v_6599) (bit_and v_6579 (eq v_6601 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6596 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2955 : imm int) (v_2959 : reg (bv 64)) => do
      v_6675 <- eval (bv_and (handleImmediateWithSignExtend v_2955 8 8) (expression.bv_nat 8 63));
      v_6676 <- eval (uge v_6675 (expression.bv_nat 8 64));
      v_6679 <- eval (eq v_6675 (expression.bv_nat 8 0));
      v_6680 <- eval (notBool_ v_6679);
      v_6681 <- getRegister v_2959;
      v_6682 <- eval (concat (expression.bv_nat 1 0) v_6681);
      v_6687 <- eval (extract (shl v_6682 (uvalueMInt (concat (expression.bv_nat 57 0) v_6675))) 0 (bitwidthMInt v_6682));
      v_6691 <- getRegister cf;
      v_6696 <- eval (bit_or (bit_and v_6676 undef) (bit_and (notBool_ v_6676) (bit_or (bit_and v_6680 (eq (extract v_6687 0 1) (expression.bv_nat 1 1))) (bit_and v_6679 (eq v_6691 (expression.bv_nat 1 1))))));
      v_6699 <- eval (eq (extract v_6687 1 2) (expression.bv_nat 1 1));
      v_6701 <- getRegister sf;
      v_6706 <- eval (bit_and v_6680 undef);
      v_6707 <- getRegister af;
      v_6712 <- eval (extract v_6687 1 65);
      v_6715 <- getRegister zf;
      v_6750 <- getRegister pf;
      v_6755 <- eval (eq v_6675 (expression.bv_nat 8 1));
      v_6760 <- getRegister of;
      setRegister (lhs.of_reg v_2959) v_6712;
      setRegister of (mux (bit_or (bit_and v_6755 (notBool_ (eq v_6696 v_6699))) (bit_and (notBool_ v_6755) (bit_or v_6706 (bit_and v_6679 (eq v_6760 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6680 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6687 64 65) (expression.bv_nat 1 1)) (eq (extract v_6687 63 64) (expression.bv_nat 1 1)))) (eq (extract v_6687 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6687 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6687 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6687 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6687 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6687 57 58) (expression.bv_nat 1 1)))) (bit_and v_6679 (eq v_6750 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6680 (eq v_6712 (expression.bv_nat 64 0))) (bit_and v_6679 (eq v_6715 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6706 (bit_and v_6679 (eq v_6707 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6680 v_6699) (bit_and v_6679 (eq v_6701 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6696 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2966 : reg (bv 64)) => do
      v_6776 <- getRegister v_2966;
      v_6777 <- eval (concat (expression.bv_nat 1 0) v_6776);
      v_6780 <- eval (extract (shl v_6777 1) 0 (bitwidthMInt v_6777));
      v_6781 <- eval (extract v_6780 0 1);
      v_6782 <- eval (extract v_6780 1 2);
      v_6783 <- eval (extract v_6780 1 65);
      setRegister (lhs.of_reg v_2966) v_6783;
      setRegister of (mux (notBool_ (eq (eq v_6781 (expression.bv_nat 1 1)) (eq v_6782 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_6780 57 65));
      setRegister zf (zeroFlag v_6783);
      setRegister af undef;
      setRegister sf v_6782;
      setRegister cf v_6781;
      pure ()
    pat_end;
    pattern fun (v_2962 : reg (bv 64)) => do
      v_9592 <- getRegister v_2962;
      v_9593 <- eval (concat (expression.bv_nat 1 0) v_9592);
      v_9596 <- eval (extract (shl v_9593 1) 0 (bitwidthMInt v_9593));
      v_9598 <- eval (eq (extract v_9596 0 1) (expression.bv_nat 1 1));
      v_9601 <- eval (eq (extract v_9596 1 2) (expression.bv_nat 1 1));
      v_9603 <- eval (extract v_9596 1 65);
      setRegister (lhs.of_reg v_2962) v_9603;
      setRegister of (mux (notBool_ (eq v_9598 v_9601)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9596 57 65));
      setRegister zf (zeroFlag v_9603);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux v_9601 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9598 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2962 : reg (bv 64)) => do
      v_9617 <- getRegister v_2962;
      v_9618 <- eval (concat (expression.bv_nat 1 0) v_9617);
      v_9621 <- eval (extract (shl v_9618 1) 0 (bitwidthMInt v_9618));
      v_9622 <- eval (extract v_9621 0 1);
      v_9623 <- eval (extract v_9621 1 2);
      v_9624 <- eval (extract v_9621 1 65);
      setRegister (lhs.of_reg v_2962) v_9624;
      setRegister of (mux (notBool_ (eq (eq v_9622 (expression.bv_nat 1 1)) (eq v_9623 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9621 57 65));
      setRegister zf (zeroFlag v_9624);
      setRegister af undef;
      setRegister sf v_9623;
      setRegister cf v_9622;
      pure ()
    pat_end;
    pattern fun cl (v_2938 : Mem) => do
      v_16013 <- evaluateAddress v_2938;
      v_16014 <- load v_16013 8;
      v_16015 <- eval (concat (expression.bv_nat 1 0) v_16014);
      v_16016 <- getRegister rcx;
      v_16018 <- eval (bv_and (extract v_16016 56 64) (expression.bv_nat 8 63));
      v_16023 <- eval (extract (shl v_16015 (uvalueMInt (concat (expression.bv_nat 57 0) v_16018))) 0 (bitwidthMInt v_16015));
      v_16024 <- eval (extract v_16023 1 65);
      store v_16013 v_16024 8;
      v_16026 <- eval (uge v_16018 (expression.bv_nat 8 64));
      v_16029 <- eval (eq v_16018 (expression.bv_nat 8 0));
      v_16030 <- eval (notBool_ v_16029);
      v_16034 <- getRegister cf;
      v_16039 <- eval (bit_or (bit_and v_16026 undef) (bit_and (notBool_ v_16026) (bit_or (bit_and v_16030 (eq (extract v_16023 0 1) (expression.bv_nat 1 1))) (bit_and v_16029 (eq v_16034 (expression.bv_nat 1 1))))));
      v_16042 <- eval (eq (extract v_16023 1 2) (expression.bv_nat 1 1));
      v_16044 <- getRegister sf;
      v_16051 <- getRegister zf;
      v_16056 <- eval (bit_and v_16030 undef);
      v_16057 <- getRegister af;
      v_16092 <- getRegister pf;
      v_16097 <- eval (eq v_16018 (expression.bv_nat 8 1));
      v_16102 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16097 (notBool_ (eq v_16039 v_16042))) (bit_and (notBool_ v_16097) (bit_or v_16056 (bit_and v_16029 (eq v_16102 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16030 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16023 64 65) (expression.bv_nat 1 1)) (eq (extract v_16023 63 64) (expression.bv_nat 1 1)))) (eq (extract v_16023 62 63) (expression.bv_nat 1 1)))) (eq (extract v_16023 61 62) (expression.bv_nat 1 1)))) (eq (extract v_16023 60 61) (expression.bv_nat 1 1)))) (eq (extract v_16023 59 60) (expression.bv_nat 1 1)))) (eq (extract v_16023 58 59) (expression.bv_nat 1 1)))) (eq (extract v_16023 57 58) (expression.bv_nat 1 1)))) (bit_and v_16029 (eq v_16092 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16056 (bit_and v_16029 (eq v_16057 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16030 (eq v_16024 (expression.bv_nat 64 0))) (bit_and v_16029 (eq v_16051 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16030 v_16042) (bit_and v_16029 (eq v_16044 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_16039 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2941 : imm int) (v_2942 : Mem) => do
      v_16115 <- evaluateAddress v_2942;
      v_16116 <- load v_16115 8;
      v_16117 <- eval (concat (expression.bv_nat 1 0) v_16116);
      v_16119 <- eval (bv_and (handleImmediateWithSignExtend v_2941 8 8) (expression.bv_nat 8 63));
      v_16124 <- eval (extract (shl v_16117 (uvalueMInt (concat (expression.bv_nat 57 0) v_16119))) 0 (bitwidthMInt v_16117));
      v_16125 <- eval (extract v_16124 1 65);
      store v_16115 v_16125 8;
      v_16127 <- eval (uge v_16119 (expression.bv_nat 8 64));
      v_16130 <- eval (eq v_16119 (expression.bv_nat 8 0));
      v_16131 <- eval (notBool_ v_16130);
      v_16135 <- getRegister cf;
      v_16140 <- eval (bit_or (bit_and v_16127 undef) (bit_and (notBool_ v_16127) (bit_or (bit_and v_16131 (eq (extract v_16124 0 1) (expression.bv_nat 1 1))) (bit_and v_16130 (eq v_16135 (expression.bv_nat 1 1))))));
      v_16143 <- eval (eq (extract v_16124 1 2) (expression.bv_nat 1 1));
      v_16145 <- getRegister sf;
      v_16152 <- getRegister zf;
      v_16157 <- eval (bit_and v_16131 undef);
      v_16158 <- getRegister af;
      v_16193 <- getRegister pf;
      v_16198 <- eval (eq v_16119 (expression.bv_nat 8 1));
      v_16203 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16198 (notBool_ (eq v_16140 v_16143))) (bit_and (notBool_ v_16198) (bit_or v_16157 (bit_and v_16130 (eq v_16203 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16131 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16124 64 65) (expression.bv_nat 1 1)) (eq (extract v_16124 63 64) (expression.bv_nat 1 1)))) (eq (extract v_16124 62 63) (expression.bv_nat 1 1)))) (eq (extract v_16124 61 62) (expression.bv_nat 1 1)))) (eq (extract v_16124 60 61) (expression.bv_nat 1 1)))) (eq (extract v_16124 59 60) (expression.bv_nat 1 1)))) (eq (extract v_16124 58 59) (expression.bv_nat 1 1)))) (eq (extract v_16124 57 58) (expression.bv_nat 1 1)))) (bit_and v_16130 (eq v_16193 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16157 (bit_and v_16130 (eq v_16158 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16131 (eq v_16125 (expression.bv_nat 64 0))) (bit_and v_16130 (eq v_16152 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16131 v_16143) (bit_and v_16130 (eq v_16145 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_16140 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2947 : Mem) => do
      v_18296 <- evaluateAddress v_2947;
      v_18297 <- load v_18296 8;
      v_18298 <- eval (concat (expression.bv_nat 1 0) v_18297);
      v_18301 <- eval (extract (shl v_18298 1) 0 (bitwidthMInt v_18298));
      v_18302 <- eval (extract v_18301 1 65);
      store v_18296 v_18302 8;
      v_18305 <- eval (eq (extract v_18301 0 1) (expression.bv_nat 1 1));
      v_18308 <- eval (eq (extract v_18301 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_18305 v_18308)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18301 57 65));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18302);
      setRegister sf (mux v_18308 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_18305 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2947 : Mem) => do
      v_18322 <- evaluateAddress v_2947;
      v_18323 <- load v_18322 8;
      v_18324 <- eval (concat (expression.bv_nat 1 0) v_18323);
      v_18327 <- eval (extract (shl v_18324 1) 0 (bitwidthMInt v_18324));
      v_18328 <- eval (extract v_18327 1 65);
      store v_18322 v_18328 8;
      v_18330 <- eval (extract v_18327 0 1);
      v_18331 <- eval (extract v_18327 1 2);
      setRegister of (mux (notBool_ (eq (eq v_18330 (expression.bv_nat 1 1)) (eq v_18331 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18327 57 65));
      setRegister af undef;
      setRegister zf (zeroFlag v_18328);
      setRegister sf v_18331;
      setRegister cf v_18330;
      pure ()
    pat_end
