def rclw1 : instruction :=
  definst "rclw" $ do
    pattern fun cl (v_2475 : reg (bv 16)) => do
      v_4137 <- getRegister rcx;
      v_4141 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4137 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4142 <- eval (extract v_4141 9 17);
      v_4143 <- eval (eq v_4142 (expression.bv_nat 8 1));
      v_4144 <- getRegister cf;
      v_4147 <- getRegister v_2475;
      v_4149 <- eval (rol (concat (mux (eq v_4144 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4147) v_4141);
      v_4150 <- eval (isBitSet v_4149 0);
      v_4156 <- eval (eq v_4142 (expression.bv_nat 8 0));
      v_4159 <- getRegister of;
      setRegister (lhs.of_reg v_2475) (extract v_4149 1 17);
      setRegister cf v_4150;
      setRegister of (bit_or (bit_and v_4143 (notBool_ (eq v_4150 (isBitSet v_4149 1)))) (bit_and (notBool_ v_4143) (bit_or (bit_and (notBool_ v_4156) undef) (bit_and v_4156 (eq v_4159 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2482 : imm int) (v_2479 : reg (bv 16)) => do
      v_4172 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2482 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4173 <- eval (extract v_4172 9 17);
      v_4174 <- eval (eq v_4173 (expression.bv_nat 8 1));
      v_4175 <- getRegister cf;
      v_4178 <- getRegister v_2479;
      v_4180 <- eval (rol (concat (mux (eq v_4175 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4178) v_4172);
      v_4181 <- eval (isBitSet v_4180 0);
      v_4187 <- eval (eq v_4173 (expression.bv_nat 8 0));
      v_4190 <- getRegister of;
      setRegister (lhs.of_reg v_2479) (extract v_4180 1 17);
      setRegister cf v_4181;
      setRegister of (bit_or (bit_and v_4174 (notBool_ (eq v_4181 (isBitSet v_4180 1)))) (bit_and (notBool_ v_4174) (bit_or (bit_and (notBool_ v_4187) undef) (bit_and v_4187 (eq v_4190 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2467 : Mem) => do
      v_11721 <- evaluateAddress v_2467;
      v_11722 <- getRegister cf;
      v_11725 <- load v_11721 2;
      v_11727 <- getRegister rcx;
      v_11731 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_11727 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_11732 <- eval (rol (concat (mux (eq v_11722 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11725) v_11731);
      store v_11721 (extract v_11732 1 17) 2;
      v_11735 <- eval (extract v_11731 9 17);
      v_11736 <- eval (eq v_11735 (expression.bv_nat 8 1));
      v_11737 <- eval (isBitSet v_11732 0);
      v_11743 <- eval (eq v_11735 (expression.bv_nat 8 0));
      v_11746 <- getRegister of;
      setRegister cf v_11737;
      setRegister of (bit_or (bit_and v_11736 (notBool_ (eq v_11737 (isBitSet v_11732 1)))) (bit_and (notBool_ v_11736) (bit_or (bit_and (notBool_ v_11743) undef) (bit_and v_11743 (eq v_11746 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2470 : imm int) (v_2471 : Mem) => do
      v_11754 <- evaluateAddress v_2471;
      v_11755 <- getRegister cf;
      v_11758 <- load v_11754 2;
      v_11763 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2470 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_11764 <- eval (rol (concat (mux (eq v_11755 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11758) v_11763);
      store v_11754 (extract v_11764 1 17) 2;
      v_11767 <- eval (extract v_11763 9 17);
      v_11768 <- eval (eq v_11767 (expression.bv_nat 8 1));
      v_11769 <- eval (isBitSet v_11764 0);
      v_11775 <- eval (eq v_11767 (expression.bv_nat 8 0));
      v_11778 <- getRegister of;
      setRegister cf v_11769;
      setRegister of (bit_or (bit_and v_11768 (notBool_ (eq v_11769 (isBitSet v_11764 1)))) (bit_and (notBool_ v_11768) (bit_or (bit_and (notBool_ v_11775) undef) (bit_and v_11775 (eq v_11778 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
