def addb1 : instruction :=
  definst "addb" $ do
    pattern fun (v_2636 : imm int) (v_2639 : reg (bv 8)) => do
      v_4478 <- eval (handleImmediateWithSignExtend v_2636 8 8);
      v_4480 <- getRegister v_2639;
      v_4482 <- eval (add (concat (expression.bv_nat 1 0) v_4478) (concat (expression.bv_nat 1 0) v_4480));
      v_4483 <- eval (extract v_4482 1 9);
      setRegister (lhs.of_reg v_2639) v_4483;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4478 v_4480) 3) (isBitSet v_4482 4)));
      setRegister cf (isBitSet v_4482 0);
      setRegister of (overflowFlag v_4478 v_4480 v_4483);
      setRegister pf (parityFlag v_4483);
      setRegister sf (isBitSet v_4482 1);
      setRegister zf (zeroFlag v_4483);
      pure ()
    pat_end;
    pattern fun (v_2652 : reg (bv 8)) (v_2653 : reg (bv 8)) => do
      v_4528 <- getRegister v_2652;
      v_4530 <- getRegister v_2653;
      v_4532 <- eval (add (concat (expression.bv_nat 1 0) v_4528) (concat (expression.bv_nat 1 0) v_4530));
      v_4533 <- eval (extract v_4532 1 9);
      setRegister (lhs.of_reg v_2653) v_4533;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4528 v_4530) 3) (isBitSet v_4532 4)));
      setRegister cf (isBitSet v_4532 0);
      setRegister of (overflowFlag v_4528 v_4530 v_4533);
      setRegister pf (parityFlag v_4533);
      setRegister sf (isBitSet v_4532 1);
      setRegister zf (zeroFlag v_4533);
      pure ()
    pat_end;
    pattern fun (v_2643 : Mem) (v_2644 : reg (bv 8)) => do
      v_8699 <- evaluateAddress v_2643;
      v_8700 <- load v_8699 1;
      v_8702 <- getRegister v_2644;
      v_8704 <- eval (add (concat (expression.bv_nat 1 0) v_8700) (concat (expression.bv_nat 1 0) v_8702));
      v_8705 <- eval (extract v_8704 1 9);
      setRegister (lhs.of_reg v_2644) v_8705;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8700 v_8702) 3) (isBitSet v_8704 4)));
      setRegister cf (isBitSet v_8704 0);
      setRegister of (overflowFlag v_8700 v_8702 v_8705);
      setRegister pf (parityFlag v_8705);
      setRegister sf (isBitSet v_8704 1);
      setRegister zf (zeroFlag v_8705);
      pure ()
    pat_end;
    pattern fun (v_2605 : imm int) (v_2608 : Mem) => do
      v_10059 <- evaluateAddress v_2608;
      v_10060 <- eval (handleImmediateWithSignExtend v_2605 8 8);
      v_10062 <- load v_10059 1;
      v_10064 <- eval (add (concat (expression.bv_nat 1 0) v_10060) (concat (expression.bv_nat 1 0) v_10062));
      v_10065 <- eval (extract v_10064 1 9);
      store v_10059 v_10065 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10060 v_10062) 3) (isBitSet v_10064 4)));
      setRegister cf (isBitSet v_10064 0);
      setRegister of (overflowFlag v_10060 v_10062 v_10065);
      setRegister pf (parityFlag v_10065);
      setRegister sf (isBitSet v_10064 1);
      setRegister zf (zeroFlag v_10065);
      pure ()
    pat_end;
    pattern fun (v_2616 : reg (bv 8)) (v_2615 : Mem) => do
      v_10107 <- evaluateAddress v_2615;
      v_10108 <- getRegister v_2616;
      v_10110 <- load v_10107 1;
      v_10112 <- eval (add (concat (expression.bv_nat 1 0) v_10108) (concat (expression.bv_nat 1 0) v_10110));
      v_10113 <- eval (extract v_10112 1 9);
      store v_10107 v_10113 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10108 v_10110) 3) (isBitSet v_10112 4)));
      setRegister cf (isBitSet v_10112 0);
      setRegister of (overflowFlag v_10108 v_10110 v_10113);
      setRegister pf (parityFlag v_10113);
      setRegister sf (isBitSet v_10112 1);
      setRegister zf (zeroFlag v_10113);
      pure ()
    pat_end
