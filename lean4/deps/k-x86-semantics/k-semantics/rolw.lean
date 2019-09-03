def rolw1 : instruction :=
  definst "rolw" $ do
    pattern fun cl (v_2645 : reg (bv 16)) => do
      v_5145 <- getRegister rcx;
      v_5147 <- eval (bv_and (extract v_5145 56 64) (expression.bv_nat 8 31));
      v_5148 <- eval (eq v_5147 (expression.bv_nat 8 0));
      v_5149 <- eval (notBool_ v_5148);
      v_5150 <- getRegister v_2645;
      v_5153 <- eval (rolHelper v_5150 (uvalueMInt (concat (expression.bv_nat 8 0) v_5147)) 0);
      v_5155 <- eval (eq (extract v_5153 15 16) (expression.bv_nat 1 1));
      v_5157 <- getRegister cf;
      v_5162 <- eval (eq v_5147 (expression.bv_nat 8 1));
      v_5170 <- getRegister of;
      setRegister (lhs.of_reg v_2645) v_5153;
      setRegister of (mux (bit_or (bit_and v_5162 (notBool_ (eq (eq (extract v_5153 0 1) (expression.bv_nat 1 1)) v_5155))) (bit_and (notBool_ v_5162) (bit_or (bit_and v_5149 undef) (bit_and v_5148 (eq v_5170 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5149 v_5155) (bit_and v_5148 (eq v_5157 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2646 : imm int) (v_2650 : reg (bv 16)) => do
      v_5181 <- eval (bv_and (handleImmediateWithSignExtend v_2646 8 8) (expression.bv_nat 8 31));
      v_5182 <- eval (eq v_5181 (expression.bv_nat 8 0));
      v_5183 <- eval (notBool_ v_5182);
      v_5184 <- getRegister v_2650;
      v_5187 <- eval (rolHelper v_5184 (uvalueMInt (concat (expression.bv_nat 8 0) v_5181)) 0);
      v_5189 <- eval (eq (extract v_5187 15 16) (expression.bv_nat 1 1));
      v_5191 <- getRegister cf;
      v_5196 <- eval (eq v_5181 (expression.bv_nat 8 1));
      v_5204 <- getRegister of;
      setRegister (lhs.of_reg v_2650) v_5187;
      setRegister of (mux (bit_or (bit_and v_5196 (notBool_ (eq (eq (extract v_5187 0 1) (expression.bv_nat 1 1)) v_5189))) (bit_and (notBool_ v_5196) (bit_or (bit_and v_5183 undef) (bit_and v_5182 (eq v_5204 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5183 v_5189) (bit_and v_5182 (eq v_5191 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2654 : reg (bv 16)) => do
      v_5214 <- getRegister v_2654;
      v_5216 <- eval (bitwidthMInt v_5214);
      v_5222 <- eval (add (extract (shl v_5214 1) 0 v_5216) (concat (mi (sub v_5216 1) 0) (extract v_5214 0 1)));
      v_5223 <- eval (extract v_5222 15 16);
      setRegister (lhs.of_reg v_2654) v_5222;
      setRegister of (mux (notBool_ (eq (eq (extract v_5222 0 1) (expression.bv_nat 1 1)) (eq v_5223 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5223;
      pure ()
    pat_end;
    pattern fun cl (v_2632 : Mem) => do
      v_14636 <- evaluateAddress v_2632;
      v_14637 <- load v_14636 2;
      v_14638 <- getRegister rcx;
      v_14640 <- eval (bv_and (extract v_14638 56 64) (expression.bv_nat 8 31));
      v_14643 <- eval (rolHelper v_14637 (uvalueMInt (concat (expression.bv_nat 8 0) v_14640)) 0);
      store v_14636 v_14643 2;
      v_14645 <- eval (eq v_14640 (expression.bv_nat 8 0));
      v_14646 <- eval (notBool_ v_14645);
      v_14648 <- eval (eq (extract v_14643 15 16) (expression.bv_nat 1 1));
      v_14650 <- getRegister cf;
      v_14655 <- eval (eq v_14640 (expression.bv_nat 8 1));
      v_14663 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14655 (notBool_ (eq (eq (extract v_14643 0 1) (expression.bv_nat 1 1)) v_14648))) (bit_and (notBool_ v_14655) (bit_or (bit_and v_14646 undef) (bit_and v_14645 (eq v_14663 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14646 v_14648) (bit_and v_14645 (eq v_14650 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2635 : imm int) (v_2636 : Mem) => do
      v_14672 <- evaluateAddress v_2636;
      v_14673 <- load v_14672 2;
      v_14675 <- eval (bv_and (handleImmediateWithSignExtend v_2635 8 8) (expression.bv_nat 8 31));
      v_14678 <- eval (rolHelper v_14673 (uvalueMInt (concat (expression.bv_nat 8 0) v_14675)) 0);
      store v_14672 v_14678 2;
      v_14680 <- eval (eq v_14675 (expression.bv_nat 8 0));
      v_14681 <- eval (notBool_ v_14680);
      v_14683 <- eval (eq (extract v_14678 15 16) (expression.bv_nat 1 1));
      v_14685 <- getRegister cf;
      v_14690 <- eval (eq v_14675 (expression.bv_nat 8 1));
      v_14698 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14690 (notBool_ (eq (eq (extract v_14678 0 1) (expression.bv_nat 1 1)) v_14683))) (bit_and (notBool_ v_14690) (bit_or (bit_and v_14681 undef) (bit_and v_14680 (eq v_14698 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14681 v_14683) (bit_and v_14680 (eq v_14685 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
