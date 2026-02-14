# SPDX-License-Identifier: MIT
# Copyright 2025-2026 Max Planck Institute for Security and Privacy (MPI-SP), University of Luebeck Institute for IT-Security (ITS)
from ip_masking_gadgets import (
    IPAESSbox,
    IPAddGadget,
    IPMultGadget,
    IPRefreshGadget,
    SecIPRefreshGadget,
)
from polymasking_gadgets import (
    BgwMultGadget,
    LaolaMultGadget,
    OptRefresh,
    FOWZ25Refresh,
    PolyAESSbox,
    RefreshSFRES18,
    SWComp,
    SWPolyAddGadget,
    SWPolyMulGadget,
    SWPolySubGadget,
)
from GCM_WCG22_gadgets import (
    GCM_L_WCG22,
    GCM22AESSbox,
    GCM_Refresh_WCG22,
    GCMMult_WCG22,
)
from GCM_WMCS20_gadgets import (
    GCM_L_WMCS20,
    GCM20AESSbox,
    GCM_Refresh_WMCS20,
    GCMMult_WMCS20,
)
from isw_gadgets import ISWMult, ISWRefresh

GADGETS = {
    g.__name__: g
    for g in (
        SWPolyAddGadget,
        SWPolySubGadget,
        SWPolyMulGadget,
        SWComp,
        FOWZ25Refresh,
        OptRefresh,
        RefreshSFRES18,
        BgwMultGadget,
        LaolaMultGadget,
        IPAddGadget,
        IPMultGadget,
        IPRefreshGadget,
        SecIPRefreshGadget,
        ISWMult,
        ISWRefresh,
        GCMMult_WMCS20,
        GCM_L_WMCS20,
        GCM_Refresh_WMCS20,
        GCMMult_WCG22,
        GCM_L_WCG22,
        GCM_Refresh_WCG22,
        PolyAESSbox,
        IPAESSbox,
        GCM20AESSbox,
        GCM22AESSbox,
    )
}
