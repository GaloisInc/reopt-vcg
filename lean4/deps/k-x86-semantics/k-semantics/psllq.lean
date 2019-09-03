def psllq1 : instruction :=
  definst "psllq" $ do
    pattern fun (v_2988 : imm int) (v_2989 : reg (bv 128)) => do
      v_7591 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2988 8 8));
      v_7593 <- getRegister v_2989;
      v_7595 <- eval (uvalueMInt v_7591);
      setRegister (lhs.of_reg v_2989) (mux (ugt v_7591 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7593 0 64) v_7595) 0 64) (extract (shl (extract v_7593 64 128) v_7595) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_2997 : reg (bv 128)) (v_2998 : reg (bv 128)) => do
      v_7608 <- getRegister v_2997;
      v_7609 <- eval (extract v_7608 64 128);
      v_7611 <- getRegister v_2998;
      v_7613 <- eval (uvalueMInt v_7609);
      setRegister (lhs.of_reg v_2998) (mux (ugt v_7609 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7611 0 64) v_7613) 0 64) (extract (shl (extract v_7611 64 128) v_7613) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_2993 : Mem) (v_2994 : reg (bv 128)) => do
      v_14433 <- evaluateAddress v_2993;
      v_14434 <- load v_14433 16;
      v_14435 <- eval (extract v_14434 64 128);
      v_14437 <- getRegister v_2994;
      v_14439 <- eval (uvalueMInt v_14435);
      setRegister (lhs.of_reg v_2994) (mux (ugt v_14435 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14437 0 64) v_14439) 0 64) (extract (shl (extract v_14437 64 128) v_14439) 0 64)));
      pure ()
    pat_end
