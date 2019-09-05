def punpcklqdq1 : instruction :=
  definst "punpcklqdq" $ do
    pattern fun (v_3279 : reg (bv 128)) (v_3280 : reg (bv 128)) => do
      v_8795 <- getRegister v_3279;
      v_8797 <- getRegister v_3280;
      setRegister (lhs.of_reg v_3280) (concat (extract v_8795 64 128) (extract v_8797 64 128));
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3275 : reg (bv 128)) => do
      v_15231 <- evaluateAddress v_3276;
      v_15232 <- load v_15231 16;
      v_15234 <- getRegister v_3275;
      setRegister (lhs.of_reg v_3275) (concat (extract v_15232 64 128) (extract v_15234 64 128));
      pure ()
    pat_end
