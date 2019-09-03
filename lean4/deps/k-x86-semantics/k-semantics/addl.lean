def addl1 : instruction :=
  definst "addl" $ do
    pattern fun (v_2580 : imm int) eax => do
      v_4647 <- eval (handleImmediateWithSignExtend v_2580 32 32);
      v_4649 <- getRegister rax;
      v_4652 <- eval (add (concat (expression.bv_nat 1 0) v_4647) (concat (expression.bv_nat 1 0) (extract v_4649 32 64)));
      v_4654 <- eval (extract v_4652 1 2);
      v_4660 <- eval (extract v_4652 1 33);
      v_4665 <- eval (eq (extract v_4647 0 1) (expression.bv_nat 1 1));
      setRegister eax v_4660;
      setRegister of (mux (bit_and (eq v_4665 (eq (extract v_4649 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_4665 (eq v_4654 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4652 25 33));
      setRegister zf (zeroFlag v_4660);
      setRegister af (bv_xor (bv_xor (extract v_4647 27 28) (extract v_4649 59 60)) (extract v_4652 28 29));
      setRegister sf v_4654;
      setRegister cf (extract v_4652 0 1);
      pure ()
    pat_end;
    pattern fun (v_2593 : imm int) (v_2592 : reg (bv 32)) => do
      v_4689 <- eval (handleImmediateWithSignExtend v_2593 32 32);
      v_4691 <- getRegister v_2592;
      v_4693 <- eval (add (concat (expression.bv_nat 1 0) v_4689) (concat (expression.bv_nat 1 0) v_4691));
      v_4695 <- eval (extract v_4693 1 2);
      v_4700 <- eval (extract v_4693 1 33);
      v_4705 <- eval (eq (extract v_4689 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2592) v_4700;
      setRegister of (mux (bit_and (eq v_4705 (eq (extract v_4691 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4705 (eq v_4695 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4693 25 33));
      setRegister zf (zeroFlag v_4700);
      setRegister af (bv_xor (extract (bv_xor v_4689 v_4691) 27 28) (extract v_4693 28 29));
      setRegister sf v_4695;
      setRegister cf (extract v_4693 0 1);
      pure ()
    pat_end;
    pattern fun (v_2601 : reg (bv 32)) (v_2602 : reg (bv 32)) => do
      v_4725 <- getRegister v_2601;
      v_4727 <- getRegister v_2602;
      v_4729 <- eval (add (concat (expression.bv_nat 1 0) v_4725) (concat (expression.bv_nat 1 0) v_4727));
      v_4731 <- eval (extract v_4729 1 2);
      v_4736 <- eval (extract v_4729 1 33);
      v_4741 <- eval (eq (extract v_4725 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2602) v_4736;
      setRegister of (mux (bit_and (eq v_4741 (eq (extract v_4727 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4741 (eq v_4731 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4729 25 33));
      setRegister zf (zeroFlag v_4736);
      setRegister af (bv_xor (extract (bv_xor v_4725 v_4727) 27 28) (extract v_4729 28 29));
      setRegister sf v_4731;
      setRegister cf (extract v_4729 0 1);
      pure ()
    pat_end;
    pattern fun (v_2596 : Mem) (v_2597 : reg (bv 32)) => do
      v_9208 <- evaluateAddress v_2596;
      v_9209 <- load v_9208 4;
      v_9211 <- getRegister v_2597;
      v_9213 <- eval (add (concat (expression.bv_nat 1 0) v_9209) (concat (expression.bv_nat 1 0) v_9211));
      v_9215 <- eval (extract v_9213 1 2);
      v_9216 <- eval (extract v_9213 1 33);
      v_9225 <- eval (eq (extract v_9209 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2597) v_9216;
      setRegister of (mux (bit_and (eq v_9225 (eq (extract v_9211 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9225 (eq v_9215 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9213 25 33));
      setRegister af (bv_xor (extract (bv_xor v_9209 v_9211) 27 28) (extract v_9213 28 29));
      setRegister zf (zeroFlag v_9216);
      setRegister sf v_9215;
      setRegister cf (extract v_9213 0 1);
      pure ()
    pat_end;
    pattern fun (v_2584 : imm int) (v_2583 : Mem) => do
      v_10953 <- evaluateAddress v_2583;
      v_10954 <- eval (handleImmediateWithSignExtend v_2584 32 32);
      v_10956 <- load v_10953 4;
      v_10958 <- eval (add (concat (expression.bv_nat 1 0) v_10954) (concat (expression.bv_nat 1 0) v_10956));
      v_10959 <- eval (extract v_10958 1 33);
      store v_10953 v_10959 4;
      v_10962 <- eval (extract v_10958 1 2);
      v_10971 <- eval (eq (extract v_10954 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10971 (eq (extract v_10956 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10971 (eq v_10962 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10958 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10954 v_10956) 27 28) (extract v_10958 28 29));
      setRegister zf (zeroFlag v_10959);
      setRegister sf v_10962;
      setRegister cf (extract v_10958 0 1);
      pure ()
    pat_end;
    pattern fun (v_2588 : reg (bv 32)) (v_2587 : Mem) => do
      v_10986 <- evaluateAddress v_2587;
      v_10987 <- getRegister v_2588;
      v_10989 <- load v_10986 4;
      v_10991 <- eval (add (concat (expression.bv_nat 1 0) v_10987) (concat (expression.bv_nat 1 0) v_10989));
      v_10992 <- eval (extract v_10991 1 33);
      store v_10986 v_10992 4;
      v_10995 <- eval (extract v_10991 1 2);
      v_11004 <- eval (eq (extract v_10987 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_11004 (eq (extract v_10989 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_11004 (eq v_10995 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10991 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10987 v_10989) 27 28) (extract v_10991 28 29));
      setRegister zf (zeroFlag v_10992);
      setRegister sf v_10995;
      setRegister cf (extract v_10991 0 1);
      pure ()
    pat_end
