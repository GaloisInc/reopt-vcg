def vpmovsxwd1 : instruction :=
  definst "vpmovsxwd" $ do
    pattern fun (v_2728 : reg (bv 128)) (v_2729 : reg (bv 128)) => do
      v_5652 <- getRegister v_2728;
      setRegister (lhs.of_reg v_2729) (concat (sext (extract v_5652 64 80) 32) (concat (sext (extract v_5652 80 96) 32) (concat (sext (extract v_5652 96 112) 32) (sext (extract v_5652 112 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2738 : reg (bv 128)) (v_2737 : reg (bv 256)) => do
      v_5669 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2737) (concat (sext (extract v_5669 0 16) 32) (concat (sext (extract v_5669 16 32) 32) (concat (sext (extract v_5669 32 48) 32) (concat (sext (extract v_5669 48 64) 32) (concat (sext (extract v_5669 64 80) 32) (concat (sext (extract v_5669 80 96) 32) (concat (sext (extract v_5669 96 112) 32) (sext (extract v_5669 112 128) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2723 : Mem) (v_2724 : reg (bv 128)) => do
      v_12059 <- evaluateAddress v_2723;
      v_12060 <- load v_12059 8;
      setRegister (lhs.of_reg v_2724) (concat (sext (extract v_12060 0 16) 32) (concat (sext (extract v_12060 16 32) 32) (concat (sext (extract v_12060 32 48) 32) (sext (extract v_12060 48 64) 32))));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2733 : reg (bv 256)) => do
      v_12073 <- evaluateAddress v_2732;
      v_12074 <- load v_12073 16;
      setRegister (lhs.of_reg v_2733) (concat (sext (extract v_12074 0 16) 32) (concat (sext (extract v_12074 16 32) 32) (concat (sext (extract v_12074 32 48) 32) (concat (sext (extract v_12074 48 64) 32) (concat (sext (extract v_12074 64 80) 32) (concat (sext (extract v_12074 80 96) 32) (concat (sext (extract v_12074 96 112) 32) (sext (extract v_12074 112 128) 32))))))));
      pure ()
    pat_end
