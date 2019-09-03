def sarb1 : instruction :=
  definst "sarb" $ do
    pattern fun cl (v_3023 : reg (bv 8)) => do
      v_7064 <- getRegister rcx;
      v_7066 <- eval (bv_and (extract v_7064 56 64) (expression.bv_nat 8 31));
      v_7067 <- eval (eq v_7066 (expression.bv_nat 8 0));
      v_7068 <- eval (notBool_ v_7067);
      v_7069 <- getRegister v_3023;
      v_7075 <- eval (ashr (mi 9 (svalueMInt (concat v_7069 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 1 0) v_7066)));
      v_7079 <- getRegister cf;
      v_7085 <- eval (eq (extract v_7075 0 1) (expression.bv_nat 1 1));
      v_7087 <- getRegister sf;
      v_7092 <- eval (extract v_7075 0 8);
      v_7095 <- getRegister zf;
      v_7100 <- eval (bit_and v_7068 undef);
      v_7101 <- getRegister af;
      v_7134 <- getRegister pf;
      v_7141 <- getRegister of;
      setRegister (lhs.of_reg v_3023) v_7092;
      setRegister of (mux (bit_and (notBool_ (eq v_7066 (expression.bv_nat 8 1))) (bit_or v_7100 (bit_and v_7067 (eq v_7141 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7068 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7075 7 8) (expression.bv_nat 1 1)) (eq (extract v_7075 6 7) (expression.bv_nat 1 1)))) (eq (extract v_7075 5 6) (expression.bv_nat 1 1)))) (eq (extract v_7075 4 5) (expression.bv_nat 1 1)))) (eq (extract v_7075 3 4) (expression.bv_nat 1 1)))) (eq (extract v_7075 2 3) (expression.bv_nat 1 1)))) (eq (extract v_7075 1 2) (expression.bv_nat 1 1)))) v_7085)) (bit_and v_7067 (eq v_7134 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7100 (bit_and v_7067 (eq v_7101 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7068 (eq v_7092 (expression.bv_nat 8 0))) (bit_and v_7067 (eq v_7095 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7068 v_7085) (bit_and v_7067 (eq v_7087 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7068 (eq (extract v_7075 8 9) (expression.bv_nat 1 1))) (bit_and v_7067 (eq v_7079 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3026 : imm int) (v_3028 : reg (bv 8)) => do
      v_7155 <- eval (bv_and (handleImmediateWithSignExtend v_3026 8 8) (expression.bv_nat 8 31));
      v_7156 <- eval (eq v_7155 (expression.bv_nat 8 0));
      v_7157 <- eval (notBool_ v_7156);
      v_7158 <- getRegister v_3028;
      v_7164 <- eval (ashr (mi 9 (svalueMInt (concat v_7158 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 1 0) v_7155)));
      v_7168 <- getRegister cf;
      v_7174 <- eval (eq (extract v_7164 0 1) (expression.bv_nat 1 1));
      v_7176 <- getRegister sf;
      v_7181 <- eval (extract v_7164 0 8);
      v_7184 <- getRegister zf;
      v_7189 <- eval (bit_and v_7157 undef);
      v_7190 <- getRegister af;
      v_7223 <- getRegister pf;
      v_7230 <- getRegister of;
      setRegister (lhs.of_reg v_3028) v_7181;
      setRegister of (mux (bit_and (notBool_ (eq v_7155 (expression.bv_nat 8 1))) (bit_or v_7189 (bit_and v_7156 (eq v_7230 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7157 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7164 7 8) (expression.bv_nat 1 1)) (eq (extract v_7164 6 7) (expression.bv_nat 1 1)))) (eq (extract v_7164 5 6) (expression.bv_nat 1 1)))) (eq (extract v_7164 4 5) (expression.bv_nat 1 1)))) (eq (extract v_7164 3 4) (expression.bv_nat 1 1)))) (eq (extract v_7164 2 3) (expression.bv_nat 1 1)))) (eq (extract v_7164 1 2) (expression.bv_nat 1 1)))) v_7174)) (bit_and v_7156 (eq v_7223 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7189 (bit_and v_7156 (eq v_7190 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7157 (eq v_7181 (expression.bv_nat 8 0))) (bit_and v_7156 (eq v_7184 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7157 v_7174) (bit_and v_7156 (eq v_7176 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7157 (eq (extract v_7164 8 9) (expression.bv_nat 1 1))) (bit_and v_7156 (eq v_7168 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3035 : reg (bv 8)) => do
      v_7245 <- getRegister v_3035;
      v_7249 <- eval (ashr (mi 9 (svalueMInt (concat v_7245 (expression.bv_nat 1 0)))) 1);
      v_7252 <- eval (extract v_7249 0 8);
      setRegister (lhs.of_reg v_3035) v_7252;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_7252);
      setRegister af undef;
      setRegister zf (zeroFlag v_7252);
      setRegister sf (extract v_7249 0 1);
      setRegister cf (extract v_7249 8 9);
      pure ()
    pat_end;
    pattern fun (v_3031 : reg (bv 8)) => do
      v_9654 <- getRegister v_3031;
      v_9658 <- eval (ashr (mi 9 (svalueMInt (concat v_9654 (expression.bv_nat 1 0)))) 1);
      v_9665 <- eval (extract v_9658 0 8);
      setRegister (lhs.of_reg v_3031) v_9665;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9665);
      setRegister zf (zeroFlag v_9665);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_9658 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9658 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3031 : reg (bv 8)) => do
      v_9675 <- getRegister v_3031;
      v_9679 <- eval (ashr (mi 9 (svalueMInt (concat v_9675 (expression.bv_nat 1 0)))) 1);
      v_9682 <- eval (extract v_9679 0 8);
      setRegister (lhs.of_reg v_3031) v_9682;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9682);
      setRegister zf (zeroFlag v_9682);
      setRegister af undef;
      setRegister sf (extract v_9679 0 1);
      setRegister cf (extract v_9679 8 9);
      pure ()
    pat_end;
    pattern fun (v_3047 : reg (bv 8)) => do
      v_9692 <- getRegister v_3047;
      v_9696 <- eval (ashr (mi 9 (svalueMInt (concat v_9692 (expression.bv_nat 1 0)))) 1);
      v_9703 <- eval (extract v_9696 0 8);
      setRegister (lhs.of_reg v_3047) v_9703;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9703);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9703);
      setRegister sf (mux (eq (extract v_9696 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9696 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3047 : reg (bv 8)) => do
      v_9713 <- getRegister v_3047;
      v_9717 <- eval (ashr (mi 9 (svalueMInt (concat v_9713 (expression.bv_nat 1 0)))) 1);
      v_9720 <- eval (extract v_9717 0 8);
      setRegister (lhs.of_reg v_3047) v_9720;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9720);
      setRegister af undef;
      setRegister zf (zeroFlag v_9720);
      setRegister sf (extract v_9717 0 1);
      setRegister cf (extract v_9717 8 9);
      pure ()
    pat_end;
    pattern fun cl (v_3009 : Mem) => do
      v_16415 <- evaluateAddress v_3009;
      v_16416 <- load v_16415 1;
      v_16420 <- getRegister rcx;
      v_16422 <- eval (bv_and (extract v_16420 56 64) (expression.bv_nat 8 31));
      v_16425 <- eval (ashr (mi 9 (svalueMInt (concat v_16416 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 1 0) v_16422)));
      v_16426 <- eval (extract v_16425 0 8);
      store v_16415 v_16426 1;
      v_16428 <- eval (eq v_16422 (expression.bv_nat 8 0));
      v_16429 <- eval (notBool_ v_16428);
      v_16433 <- getRegister cf;
      v_16439 <- eval (eq (extract v_16425 0 1) (expression.bv_nat 1 1));
      v_16441 <- getRegister sf;
      v_16448 <- getRegister zf;
      v_16453 <- eval (bit_and v_16429 undef);
      v_16454 <- getRegister af;
      v_16487 <- getRegister pf;
      v_16494 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16422 (expression.bv_nat 8 1))) (bit_or v_16453 (bit_and v_16428 (eq v_16494 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16429 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16425 7 8) (expression.bv_nat 1 1)) (eq (extract v_16425 6 7) (expression.bv_nat 1 1)))) (eq (extract v_16425 5 6) (expression.bv_nat 1 1)))) (eq (extract v_16425 4 5) (expression.bv_nat 1 1)))) (eq (extract v_16425 3 4) (expression.bv_nat 1 1)))) (eq (extract v_16425 2 3) (expression.bv_nat 1 1)))) (eq (extract v_16425 1 2) (expression.bv_nat 1 1)))) v_16439)) (bit_and v_16428 (eq v_16487 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16453 (bit_and v_16428 (eq v_16454 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16429 (eq v_16426 (expression.bv_nat 8 0))) (bit_and v_16428 (eq v_16448 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16429 v_16439) (bit_and v_16428 (eq v_16441 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16429 (eq (extract v_16425 8 9) (expression.bv_nat 1 1))) (bit_and v_16428 (eq v_16433 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3013 : imm int) (v_3012 : Mem) => do
      v_16506 <- evaluateAddress v_3012;
      v_16507 <- load v_16506 1;
      v_16512 <- eval (bv_and (handleImmediateWithSignExtend v_3013 8 8) (expression.bv_nat 8 31));
      v_16515 <- eval (ashr (mi 9 (svalueMInt (concat v_16507 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 1 0) v_16512)));
      v_16516 <- eval (extract v_16515 0 8);
      store v_16506 v_16516 1;
      v_16518 <- eval (eq v_16512 (expression.bv_nat 8 0));
      v_16519 <- eval (notBool_ v_16518);
      v_16523 <- getRegister cf;
      v_16529 <- eval (eq (extract v_16515 0 1) (expression.bv_nat 1 1));
      v_16531 <- getRegister sf;
      v_16538 <- getRegister zf;
      v_16543 <- eval (bit_and v_16519 undef);
      v_16544 <- getRegister af;
      v_16577 <- getRegister pf;
      v_16584 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16512 (expression.bv_nat 8 1))) (bit_or v_16543 (bit_and v_16518 (eq v_16584 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16519 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16515 7 8) (expression.bv_nat 1 1)) (eq (extract v_16515 6 7) (expression.bv_nat 1 1)))) (eq (extract v_16515 5 6) (expression.bv_nat 1 1)))) (eq (extract v_16515 4 5) (expression.bv_nat 1 1)))) (eq (extract v_16515 3 4) (expression.bv_nat 1 1)))) (eq (extract v_16515 2 3) (expression.bv_nat 1 1)))) (eq (extract v_16515 1 2) (expression.bv_nat 1 1)))) v_16529)) (bit_and v_16518 (eq v_16577 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16543 (bit_and v_16518 (eq v_16544 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16519 (eq v_16516 (expression.bv_nat 8 0))) (bit_and v_16518 (eq v_16538 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16519 v_16529) (bit_and v_16518 (eq v_16531 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16519 (eq (extract v_16515 8 9) (expression.bv_nat 1 1))) (bit_and v_16518 (eq v_16523 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3016 : Mem) => do
      v_18111 <- evaluateAddress v_3016;
      v_18112 <- load v_18111 1;
      v_18116 <- eval (ashr (mi 9 (svalueMInt (concat v_18112 (expression.bv_nat 1 0)))) 1);
      v_18117 <- eval (extract v_18116 0 8);
      store v_18111 v_18117 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_18117);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18117);
      setRegister sf (mux (eq (extract v_18116 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18116 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3016 : Mem) => do
      v_18133 <- evaluateAddress v_3016;
      v_18134 <- load v_18133 1;
      v_18138 <- eval (ashr (mi 9 (svalueMInt (concat v_18134 (expression.bv_nat 1 0)))) 1);
      v_18139 <- eval (extract v_18138 0 8);
      store v_18133 v_18139 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_18139);
      setRegister af undef;
      setRegister zf (zeroFlag v_18139);
      setRegister sf (extract v_18138 0 1);
      setRegister cf (extract v_18138 8 9);
      pure ()
    pat_end
