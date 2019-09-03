def rolq1 : instruction :=
  definst "rolq" $ do
    pattern fun cl (v_2622 : reg (bv 64)) => do
      v_5047 <- getRegister rcx;
      v_5049 <- eval (bv_and (extract v_5047 56 64) (expression.bv_nat 8 63));
      v_5050 <- eval (eq v_5049 (expression.bv_nat 8 0));
      v_5051 <- eval (notBool_ v_5050);
      v_5052 <- getRegister v_2622;
      v_5055 <- eval (rolHelper v_5052 (uvalueMInt (concat (expression.bv_nat 56 0) v_5049)) 0);
      v_5057 <- eval (eq (extract v_5055 63 64) (expression.bv_nat 1 1));
      v_5059 <- getRegister cf;
      v_5064 <- eval (eq v_5049 (expression.bv_nat 8 1));
      v_5072 <- getRegister of;
      setRegister (lhs.of_reg v_2622) v_5055;
      setRegister of (mux (bit_or (bit_and v_5064 (notBool_ (eq (eq (extract v_5055 0 1) (expression.bv_nat 1 1)) v_5057))) (bit_and (notBool_ v_5064) (bit_or (bit_and v_5051 undef) (bit_and v_5050 (eq v_5072 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5051 v_5057) (bit_and v_5050 (eq v_5059 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2623 : imm int) (v_2627 : reg (bv 64)) => do
      v_5083 <- eval (bv_and (handleImmediateWithSignExtend v_2623 8 8) (expression.bv_nat 8 63));
      v_5084 <- eval (eq v_5083 (expression.bv_nat 8 0));
      v_5085 <- eval (notBool_ v_5084);
      v_5086 <- getRegister v_2627;
      v_5089 <- eval (rolHelper v_5086 (uvalueMInt (concat (expression.bv_nat 56 0) v_5083)) 0);
      v_5091 <- eval (eq (extract v_5089 63 64) (expression.bv_nat 1 1));
      v_5093 <- getRegister cf;
      v_5098 <- eval (eq v_5083 (expression.bv_nat 8 1));
      v_5106 <- getRegister of;
      setRegister (lhs.of_reg v_2627) v_5089;
      setRegister of (mux (bit_or (bit_and v_5098 (notBool_ (eq (eq (extract v_5089 0 1) (expression.bv_nat 1 1)) v_5091))) (bit_and (notBool_ v_5098) (bit_or (bit_and v_5085 undef) (bit_and v_5084 (eq v_5106 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5085 v_5091) (bit_and v_5084 (eq v_5093 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2631 : reg (bv 64)) => do
      v_5116 <- getRegister v_2631;
      v_5118 <- eval (bitwidthMInt v_5116);
      v_5124 <- eval (add (extract (shl v_5116 1) 0 v_5118) (concat (mi (sub v_5118 1) 0) (extract v_5116 0 1)));
      v_5125 <- eval (extract v_5124 63 64);
      setRegister (lhs.of_reg v_2631) v_5124;
      setRegister of (mux (notBool_ (eq (eq (extract v_5124 0 1) (expression.bv_nat 1 1)) (eq v_5125 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5125;
      pure ()
    pat_end;
    pattern fun cl (v_2609 : Mem) => do
      v_14483 <- evaluateAddress v_2609;
      v_14484 <- load v_14483 8;
      v_14485 <- getRegister rcx;
      v_14487 <- eval (bv_and (extract v_14485 56 64) (expression.bv_nat 8 63));
      v_14490 <- eval (rolHelper v_14484 (uvalueMInt (concat (expression.bv_nat 56 0) v_14487)) 0);
      store v_14483 v_14490 8;
      v_14492 <- eval (eq v_14487 (expression.bv_nat 8 0));
      v_14493 <- eval (notBool_ v_14492);
      v_14495 <- eval (eq (extract v_14490 63 64) (expression.bv_nat 1 1));
      v_14497 <- getRegister cf;
      v_14502 <- eval (eq v_14487 (expression.bv_nat 8 1));
      v_14510 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14502 (notBool_ (eq (eq (extract v_14490 0 1) (expression.bv_nat 1 1)) v_14495))) (bit_and (notBool_ v_14502) (bit_or (bit_and v_14493 undef) (bit_and v_14492 (eq v_14510 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14493 v_14495) (bit_and v_14492 (eq v_14497 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2612 : imm int) (v_2613 : Mem) => do
      v_14519 <- evaluateAddress v_2613;
      v_14520 <- load v_14519 8;
      v_14522 <- eval (bv_and (handleImmediateWithSignExtend v_2612 8 8) (expression.bv_nat 8 63));
      v_14525 <- eval (rolHelper v_14520 (uvalueMInt (concat (expression.bv_nat 56 0) v_14522)) 0);
      store v_14519 v_14525 8;
      v_14527 <- eval (eq v_14522 (expression.bv_nat 8 0));
      v_14528 <- eval (notBool_ v_14527);
      v_14530 <- eval (eq (extract v_14525 63 64) (expression.bv_nat 1 1));
      v_14532 <- getRegister cf;
      v_14537 <- eval (eq v_14522 (expression.bv_nat 8 1));
      v_14545 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14537 (notBool_ (eq (eq (extract v_14525 0 1) (expression.bv_nat 1 1)) v_14530))) (bit_and (notBool_ v_14537) (bit_or (bit_and v_14528 undef) (bit_and v_14527 (eq v_14545 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14528 v_14530) (bit_and v_14527 (eq v_14532 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
