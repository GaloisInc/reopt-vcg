def pinsrd1 : instruction :=
  definst "pinsrd" $ do
    pattern fun (v_2517 : imm int) (v_2520 : reg (bv 32)) (v_2518 : reg (bv 128)) => do
      v_4410 <- getRegister v_2518;
      v_4416 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2517 8 8) 6 8)) 5) 0 128));
      v_4418 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_4416) 0 128);
      v_4421 <- getRegister v_2520;
      setRegister (lhs.of_reg v_2518) (bv_or (bv_and v_4410 (bv_xor v_4418 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_4421) v_4416) 0 128) v_4418));
      pure ()
    pat_end;
    pattern fun (v_2513 : imm int) (v_2512 : Mem) (v_2514 : reg (bv 128)) => do
      v_11518 <- getRegister v_2514;
      v_11524 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2513 8 8) 6 8)) 5) 0 128));
      v_11526 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_11524) 0 128);
      v_11529 <- evaluateAddress v_2512;
      v_11530 <- load v_11529 4;
      setRegister (lhs.of_reg v_2514) (bv_or (bv_and v_11518 (bv_xor v_11526 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_11530) v_11524) 0 128) v_11526));
      pure ()
    pat_end
