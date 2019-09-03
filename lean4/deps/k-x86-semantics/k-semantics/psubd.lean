def psubd1 : instruction :=
  definst "psubd" $ do
    pattern fun (v_3104 : reg (bv 128)) (v_3105 : reg (bv 128)) => do
      v_8081 <- getRegister v_3105;
      v_8083 <- getRegister v_3104;
      setRegister (lhs.of_reg v_3105) (concat (sub (extract v_8081 0 32) (extract v_8083 0 32)) (concat (sub (extract v_8081 32 64) (extract v_8083 32 64)) (concat (sub (extract v_8081 64 96) (extract v_8083 64 96)) (sub (extract v_8081 96 128) (extract v_8083 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3100 : Mem) (v_3101 : reg (bv 128)) => do
      v_14696 <- getRegister v_3101;
      v_14698 <- evaluateAddress v_3100;
      v_14699 <- load v_14698 16;
      setRegister (lhs.of_reg v_3101) (concat (sub (extract v_14696 0 32) (extract v_14699 0 32)) (concat (sub (extract v_14696 32 64) (extract v_14699 32 64)) (concat (sub (extract v_14696 64 96) (extract v_14699 64 96)) (sub (extract v_14696 96 128) (extract v_14699 96 128)))));
      pure ()
    pat_end
