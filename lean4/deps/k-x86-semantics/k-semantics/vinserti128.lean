def vinserti1281 : instruction :=
  definst "vinserti128" $ do
    pattern fun (v_2481 : imm int) (v_2480 : reg (bv 128)) (v_2478 : reg (bv 256)) (v_2479 : reg (bv 256)) => do
      v_4577 <- getRegister v_2478;
      v_4579 <- getRegister v_2480;
      setRegister (lhs.of_reg v_2479) (mux (eq (extract (handleImmediateWithSignExtend v_2481 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_4577 0 128) v_4579) (concat v_4579 (extract v_4577 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2475 : imm int) (v_2472 : Mem) (v_2473 : reg (bv 256)) (v_2474 : reg (bv 256)) => do
      v_10625 <- getRegister v_2473;
      v_10627 <- evaluateAddress v_2472;
      v_10628 <- load v_10627 16;
      setRegister (lhs.of_reg v_2474) (mux (eq (extract (handleImmediateWithSignExtend v_2475 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_10625 0 128) v_10628) (concat v_10628 (extract v_10625 128 256)));
      pure ()
    pat_end
