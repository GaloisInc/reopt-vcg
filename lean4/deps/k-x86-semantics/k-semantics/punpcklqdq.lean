def punpcklqdq1 : instruction :=
  definst "punpcklqdq" $ do
    pattern fun (v_3230 : reg (bv 128)) (v_3231 : reg (bv 128)) => do
      v_8861 <- getRegister v_3230;
      v_8863 <- getRegister v_3231;
      setRegister (lhs.of_reg v_3231) (concat (extract v_8861 64 128) (extract v_8863 64 128));
      pure ()
    pat_end;
    pattern fun (v_3226 : Mem) (v_3227 : reg (bv 128)) => do
      v_15434 <- evaluateAddress v_3226;
      v_15435 <- load v_15434 16;
      v_15437 <- getRegister v_3227;
      setRegister (lhs.of_reg v_3227) (concat (extract v_15435 64 128) (extract v_15437 64 128));
      pure ()
    pat_end
