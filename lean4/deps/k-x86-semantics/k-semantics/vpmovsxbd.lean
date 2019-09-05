def vpmovsxbd1 : instruction :=
  definst "vpmovsxbd" $ do
    pattern fun (v_2656 : reg (bv 128)) (v_2657 : reg (bv 128)) => do
      v_5468 <- getRegister v_2656;
      setRegister (lhs.of_reg v_2657) (concat (sext (extract v_5468 96 104) 32) (concat (sext (extract v_5468 104 112) 32) (concat (sext (extract v_5468 112 120) 32) (sext (extract v_5468 120 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2666 : reg (bv 128)) (v_2665 : reg (bv 256)) => do
      v_5485 <- getRegister v_2666;
      setRegister (lhs.of_reg v_2665) (concat (sext (extract v_5485 64 72) 32) (concat (sext (extract v_5485 72 80) 32) (concat (sext (extract v_5485 80 88) 32) (concat (sext (extract v_5485 88 96) 32) (concat (sext (extract v_5485 96 104) 32) (concat (sext (extract v_5485 104 112) 32) (concat (sext (extract v_5485 112 120) 32) (sext (extract v_5485 120 128) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2651 : Mem) (v_2652 : reg (bv 128)) => do
      v_11899 <- evaluateAddress v_2651;
      v_11900 <- load v_11899 4;
      setRegister (lhs.of_reg v_2652) (concat (sext (extract v_11900 0 8) 32) (concat (sext (extract v_11900 8 16) 32) (concat (sext (extract v_11900 16 24) 32) (sext (extract v_11900 24 32) 32))));
      pure ()
    pat_end;
    pattern fun (v_2660 : Mem) (v_2661 : reg (bv 256)) => do
      v_11913 <- evaluateAddress v_2660;
      v_11914 <- load v_11913 8;
      setRegister (lhs.of_reg v_2661) (concat (sext (extract v_11914 0 8) 32) (concat (sext (extract v_11914 8 16) 32) (concat (sext (extract v_11914 16 24) 32) (concat (sext (extract v_11914 24 32) 32) (concat (sext (extract v_11914 32 40) 32) (concat (sext (extract v_11914 40 48) 32) (concat (sext (extract v_11914 48 56) 32) (sext (extract v_11914 56 64) 32))))))));
      pure ()
    pat_end
