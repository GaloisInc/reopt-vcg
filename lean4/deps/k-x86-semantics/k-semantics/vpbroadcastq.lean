def vpbroadcastq1 : instruction :=
  definst "vpbroadcastq" $ do
    pattern fun (v_2733 : reg (bv 128)) (v_2734 : reg (bv 128)) => do
      v_7068 <- getRegister v_2733;
      setRegister (lhs.of_reg v_2734) (concat (extract v_7068 64 128) (extract v_7068 64 128));
      pure ()
    pat_end;
    pattern fun (v_2742 : reg (bv 128)) (v_2746 : reg (bv 256)) => do
      v_7076 <- getRegister v_2742;
      setRegister (lhs.of_reg v_2746) (concat (concat (extract v_7076 64 128) (extract v_7076 64 128)) (concat (extract v_7076 64 128) (extract v_7076 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2729 : reg (bv 128)) => do
      v_15949 <- evaluateAddress v_2732;
      v_15950 <- load v_15949 8;
      setRegister (lhs.of_reg v_2729) (concat v_15950 v_15950);
      pure ()
    pat_end;
    pattern fun (v_2740 : Mem) (v_2741 : reg (bv 256)) => do
      v_15953 <- evaluateAddress v_2740;
      v_15954 <- load v_15953 8;
      setRegister (lhs.of_reg v_2741) (concat (concat v_15954 v_15954) (concat v_15954 v_15954));
      pure ()
    pat_end
