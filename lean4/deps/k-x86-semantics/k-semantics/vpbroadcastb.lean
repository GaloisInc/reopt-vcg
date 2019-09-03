def vpbroadcastb1 : instruction :=
  definst "vpbroadcastb" $ do
    pattern fun (v_2687 : reg (bv 128)) (v_2688 : reg (bv 128)) => do
      v_7124 <- getRegister v_2687;
      v_7125 <- eval (extract v_7124 120 128);
      setRegister (lhs.of_reg v_2688) (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 (concat v_7125 v_7125)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2696 : reg (bv 128)) (v_2697 : reg (bv 256)) => do
      v_7146 <- getRegister v_2696;
      v_7147 <- eval (extract v_7146 120 128);
      setRegister (lhs.of_reg v_2697) (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 (concat v_7147 v_7147)))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2682 : Mem) (v_2683 : reg (bv 128)) => do
      v_16393 <- evaluateAddress v_2682;
      v_16394 <- load v_16393 1;
      setRegister (lhs.of_reg v_2683) (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 (concat v_16394 v_16394)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2691 : Mem) (v_2692 : reg (bv 256)) => do
      v_16411 <- evaluateAddress v_2691;
      v_16412 <- load v_16411 1;
      setRegister (lhs.of_reg v_2692) (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 (concat v_16412 v_16412)))))))))))))))))))))))))))))));
      pure ()
    pat_end
